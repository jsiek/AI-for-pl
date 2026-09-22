module strong-rep-store.Residual where

-- File Charter:
--   * ONE-HOLE TERM CONTEXTS, THE SCOPE MAP AT A HOLE, AND RESIDUALS.
--     This is the layer the COLOR PRESERVATION theorem
--     (strong-rep-store.ColorPreservation) is stated in.  §1 is `TermCtx`
--     with `plug`; §2 is `_⊢C_⊣_`, the type context AT THE HOLE — the
--     hole's SCOPE MAP is its `names`; §3 renames a context in the
--     REPRESENTATION UNIVERSE exactly as `renᴹᴿ` renames a term, and
--     reads off the renaming that reaches the hole; §4 pushes `Beta`'s
--     substitution through a context; §5 is `Residual`, ONE STEP, and §6
--     `Residuals`, a whole run.
--   * WHAT A RESIDUAL RECORDS (2026-09-21, the v7 restatement).  A
--     position is a pair `(C , M)`, the hole and the node in it.  A step
--     moves a retained node to a new position `(D , N)`, and every move
--     in this calculus except `TyBeta`'s refinement is
--     REPRESENTATION-ONLY (proof/ShiftAudit §3): the node is `M` renamed
--     by some `renᴹᴿ ρ`, so the residual relation carries that `ρ` — the
--     representation renaming that reaches the hole — as an index.
--     `Residuals` composes them along a run.  The theorem then says the
--     scope map at `D` is the scope map at `C` under `ρ`.
--   * WHAT THE STORE CHANGED (experiment 2, 2026-09-22,
--     notes/RepStoreSketch.md).  A boundary no longer carries a bind
--     block, so NO rule moves a subterm past one: the only
--     representation move left is the UNIFORM SIBLING SHIFT a step's
--     allocation imposes — `suc` when the step returns `new R`, the
--     identity when it returns `none` (`↑ᶜ[_]`/`↑ᴴ[_]`/`↑ʳ[_]` in §3).
--     `Peel`'s argument therefore moves VERBATIM (`dual-interior` lands
--     it at the exterior itself), and the redex's own contractum keeps
--     `idᵗ`: `TyBeta`'s and `TyPeelR-Λ`'s body sits under the `Λ` binder
--     that BECOMES the allocated cell, so its indices are already right.
--     The one position that still moves inside a redex is
--     `TyPeelR-⟪⟫`'s inner boundary, a SIBLING of that `Λ`, which gets
--     exactly `suc`.  What went with the bind block: the paired
--     `renCtx²`/`holeRen²`, whose boundary clause stepped past
--     `numBinds Θ` representation binders, and the `moveᴿ` wrapper —
--     §3 is now the representation-only `renCtxᴿ`/`holeᴿ`.
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
--     step's contractum is strong-rep-store.proof.Residual, and the
--     theorem is strong-rep-store.proof.ColorPreservation.

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
    δ : Alloc

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
-- 3. Renaming a context in the REPRESENTATION universe, clause for
--    clause with `renᴹᴿ`, and the renaming that reaches its hole: only a
--    `Λ` frame changes it, and a boundary frame does not — crossing a
--    boundary no longer crosses a bind block.
------------------------------------------------------------------------

renCtxᴿ : Renameᵗ → TermCtx → TermCtx
renCtxᴿ ρ □               = □
renCtxᴿ ρ (ƛC A ∙ C)      = ƛC A ∙ renCtxᴿ ρ C
renCtxᴿ ρ (C ·L N)        = renCtxᴿ ρ C ·L renᴹᴿ ρ N
renCtxᴿ ρ (L ·R C)        = renᴹᴿ ρ L ·R renCtxᴿ ρ C
renCtxᴿ ρ (ΛC C)          = ΛC (renCtxᴿ (extᵗ ρ) C)
renCtxᴿ ρ (C ·C[ B , A ]) = renCtxᴿ ρ C ·C[ B , A ]
renCtxᴿ ρ (C ⟪C Θ , c ⟫)  = renCtxᴿ ρ C ⟪C renᴮᴿ ρ Θ , c ⟫

holeᴿ : Renameᵗ → TermCtx → Renameᵗ
holeᴿ ρ □               = ρ
holeᴿ ρ (ƛC A ∙ C)      = holeᴿ ρ C
holeᴿ ρ (C ·L N)        = holeᴿ ρ C
holeᴿ ρ (L ·R C)        = holeᴿ ρ C
holeᴿ ρ (ΛC C)          = holeᴿ (extᵗ ρ) C
holeᴿ ρ (C ·C[ B , A ]) = holeᴿ ρ C
holeᴿ ρ (C ⟪C Θ , c ⟫)  = holeᴿ ρ C

-- THE SIBLING SHIFT AT A POSITION.  A step returns the change `δ` it
-- made to the store and the congruences shift the redex's siblings by
-- `↑ᴹ[ δ ]` (strong-rep-store.TermSubst §2).  A position inside such a
-- sibling therefore moves by the same shift, split into its three
-- halves: the context around it, the node in it, and the renaming that
-- reaches the hole.  At `none` all three are the identity ON THE NOSE,
-- which is what keeps the `_-→_∣ none` rules' residuals `idᵗ`.
↑ᶜ[_] : Alloc → TermCtx → TermCtx
↑ᶜ[ none  ] C = C
↑ᶜ[ new R ] C = renCtxᴿ suc C

↑ᴴ[_] : Alloc → TermCtx → Term → Term
↑ᴴ[ none  ] C M = M
↑ᴴ[ new R ] C M = renᴹᴿ (holeᴿ suc C) M

↑ʳ[_] : Alloc → TermCtx → Renameᵗ
↑ʳ[ none  ] C = idᵗ
↑ʳ[ new R ] C = holeᴿ suc C

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
        (renCtxᴿ suc D ⟪C boundary (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
        (renᴹᴿ (holeᴿ suc D) N)

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
--    proof/ShiftAudit §1's table; `ρ` is that table's third column, and
--    since the store it is `idᵗ` everywhere but in `TyPeelR-⟪⟫`'s moved
--    boundary and in a sibling the allocating step shifted.
------------------------------------------------------------------------

data Residual : ∀ {Δ L L′ δ} → Δ ⊢ L -→ L′ ∣ δ
              → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where

  -- TyBeta: the body stays where it is; its `Λ` slot BECOMES the
  -- allocated cell (refinement `abstR → bindR R`, no move), and the
  -- scope `instantiate (boundary [])` re-unlocks the body's own name for
  -- it — so the body's indices are already right and ρ is `idᵗ`.
  residual-TyBeta : ∀ {R C M}
    (vN : Value (plug C M)) (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyBeta {Δ = Δ} {B = B} {A = A} {N = plug C M} vN pA)
        ((ΛC C) ·C[ B , A ]) M idᵗ
        (C ⟪C instantiate (boundary []) , reveal 0 B ⟫) M

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
        ((C ·L (W ⟪ dualBoundary Θ , s′ ⟫)) ⟪C Θ , t ⟫) M

  -- Peel, the argument: it crosses into the dual VERBATIM.  There is no
  -- bind block to cross any more, and `dual-interior` lands the dual's
  -- interior at the exterior itself, so ρ is `idᵗ`.
  residual-Peel-arg : ∀ {Δᶜ Δᵈ V C M s s′ t}
    (vV : Value V) (vW : Value (plug C M))
    (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ) (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ)
    (rd : Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ) (sc : SameConv Δᵈ s′ Δᶜ s)
    → Residual (Peel {V = V} {W = plug C M} {t = t} vV vW rc ri rd sc)
        ((V ⟪ Θ , s ↦ t ⟫) ·R C) M idᵗ
        ((V ·R (C ⟪C dualBoundary Θ , s′ ⟫)) ⟪C Θ , t ⟫) M

  -- TyPeelR-Λ: as TyBeta, one boundary in — the body's `Λ` slot becomes
  -- the allocated cell the instantiated scope unlocks.
  residual-TyPeelR-Λ : ∀ {Δᶜ C M s R Bᵢ Bₑ}
    (vN : Value (plug C M))
    (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ) (⊢s : underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
    (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyPeelR-Λ {N = plug C M} {B = B} vN rc ⊢s pA)
        (((ΛC C) ⟪C Θ , `∀ s ⟫) ·C[ B , A ]) M idᵗ
        (C ⟪C instantiate Θ , instReveal 0 s ⟫) M

  -- TyPeelR-⟪⟫: the inner boundary is a SIBLING of the `Λ` slot the
  -- allocation consumes, so its interior gets exactly the sibling shift
  -- `suc` — the one non-identity ρ a redex still produces.
  residual-TyPeelR-⟪⟫ : ∀ {Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ C M Θ′ s′ s″ s R Bᵢ Bᵢ′ Bₑ}
    (vW : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ) (rc : Δ ⊢ᶜ Θ ⇒ Δᶜ)
    (rc′ : Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ)
    (ri⁺ : allocate R Δ ⊢ⁱ instantiate Θ ⇒ Δᵢ⁺)
    (rc″ : Δᵢ⁺ ⊢ᶜ addLock0 (renᴮᴿ suc Θ′) ⇒ Δ″ᶜ)
    (sc : SameConv (underΛ Δ″ᶜ) s″
            (underΛ (renNameCtx suc Δ″ᶜ Δ′ᶜ)) s′)
    (⊢s : underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ)
    (sm : underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ)
    (pA : Δ ⊢ᶜ A ~ R)
    → Residual (TyPeelR-⟪⟫ {W = plug C M} {B = B}
                 vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA)
        (((C ⟪C Θ′ , `∀ s′ ⟫) ⟪C Θ , `∀ s ⟫) ·C[ B , A ]) M
        (holeᴿ suc C)
        (((renCtxᴿ suc C ⟪C addLock0 (renᴮᴿ suc Θ′) , `∀ s″ ⟫)
            ·C[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
           ⟪C instantiate Θ , instReveal 0 s ⟫)
        (renᴹᴿ (holeᴿ suc C) M)

  -- CancelR and IdPush: the value keeps its frame under both the merged
  -- and the rewound scope (proof/ShiftAudit §6).
  residual-CancelR : ∀ {Δ₁ᶜ Δ⋉ᶜ Δᶜ C M Θ₁ Θ₂ X Y A′ Aᵢ}
    (vV : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) (rc₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
    (lX : Δ₁ᶜ ∋ X := Aᵢ)
    (rc⋉ : Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
    (sm : Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ)
    (rc₂ : Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) (lY : Δᶜ ∋ Y := A)
    → Residual (CancelR {V = plug C M} vV ri rc₁ lX rc⋉ sm rc₂ lY)
        ((C ⟪C Θ₁ , seal X ⟫) ⟪C Θ₂ , unseal Y ⟫) M idᵗ
        ((C ⟪C Θ₁ ⋉ Θ₂ , mkId A′ ⟫) ⟪C rewind Θ₂ , mkId A ⟫) M

  residual-IdPush : ∀ {Δ₁ᶜ Δ⋉ᶜ Δᶜ C M Θ₁ Θ₂ X X′ Y}
    (vV : Value (plug C M))
    (ri : Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) (rc₁ : Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ)
    (rc⋉ : Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ)
    (sm : Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ)
    (rc₂ : Δ ⊢ᶜ Θ₂ ⇒ Δᶜ) (lY : Δᶜ ∋ Y := A)
    → Residual (IdPush {V = plug C M} vV ri rc₁ rc⋉ sm rc₂ lY)
        ((C ⟪C Θ₁ , id (` X) ⟫) ⟪C Θ₂ , unseal Y ⟫) M idᵗ
        ((C ⟪C Θ₁ ⋉ Θ₂ , unseal X′ ⟫) ⟪C rewind Θ₂ , mkId A ⟫) M

  -- (Drop$, Drop-true, Drop-false: no residual — the literal is consumed
  -- with its boundary.)

  -- The ξ rules: the position is inside the stepping subterm, or in the
  -- SIBLING that stands still — and a sibling moves by the step's own
  -- store change, `↑ᶜ[ δ ]`/`↑ᴴ[ δ ]`/`↑ʳ[ δ ]`.
  residual-ξ-·-l : ∀ {L′ C M D N} {r : Δ ⊢ L -→ L′ ∣ δ}
    → Residual r C M ρ D N
    → Residual (ξ-·-l {M = P} r) (C ·L P) M ρ (D ·L ↑ᴹ[ δ ] P) N
  residual-ξ-·-l-sib : ∀ {L′ C M} (r : Δ ⊢ L -→ L′ ∣ δ)
    → Residual (ξ-·-l {M = plug C M} r) (L ·R C) M (↑ʳ[ δ ] C)
        (L′ ·R ↑ᶜ[ δ ] C) (↑ᴴ[ δ ] C M)
  residual-ξ-·-r : ∀ {V P′ C M D N} {r : Δ ⊢ P -→ P′ ∣ δ}
    (v : Value V) → Residual r C M ρ D N
    → Residual (ξ-·-r v r) (V ·R C) M ρ (↑ᴹ[ δ ] V ·R D) N
  residual-ξ-·-r-sib : ∀ {P′ C M} (v : Value (plug C M))
    (r : Δ ⊢ P -→ P′ ∣ δ)
    → Residual (ξ-·-r v r) (C ·L P) M (↑ʳ[ δ ] C)
        (↑ᶜ[ δ ] C ·L P′) (↑ᴴ[ δ ] C M)
  residual-ξ-·[] : ∀ {L′ C M D N} {r : Δ ⊢ L -→ L′ ∣ δ}
    → Residual r C M ρ D N
    → Residual (ξ-·[] {B = B} {A = A} r)
        (C ·C[ B , A ]) M ρ (D ·C[ B , A ]) N
  residual-ξ-⟪⟫ : ∀ {M′ C O D O′} {r : Δᵢ ⊢ N -→ M′ ∣ δ}
    (ri : Δ ⊢ⁱ Θ ⇒ Δᵢ) → Residual r C O ρ D O′
    → Residual (ξ-⟪⟫ {c = c} ri r) (C ⟪C Θ , c ⟫) O ρ
        (D ⟪C ↑ᴮ[ δ ] Θ , c ⟫) O′

------------------------------------------------------------------------
-- 6. Residuals through a run: the renamings compose, and each step's
--    store change is applied to the context its tail runs at.
------------------------------------------------------------------------

data Residuals : ∀ {Δ L L′} → Δ ⊢ L -→* L′
               → TermCtx → Term → Renameᵗ → TermCtx → Term → Set where
  residuals-done : ∀ {C M}
    → Residuals (done {Δ = Δ} {M = plug C M}) C M idᵗ C M
  residuals-step : ∀ {L′ L″ C M ρ′ D N E O}
    {r : Δ ⊢ L -→ L′ ∣ δ} {rs : apply δ Δ ⊢ L′ -→* L″}
    → Residual r C M ρ D N
    → Residuals rs D N ρ′ E O
    → Residuals (r then rs) C M (ρ′ ∘ ρ) E O
