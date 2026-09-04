module strong.BReduction where

-- Reduction for the tight dual boundary (B₀) design, one rule at a time.
-- Each rule: the rule, a worked typed example, and its preservation case.
-- Preservation is stated at runtime term contexts ([]).

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _⊔_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; +-monoʳ-<; +-cancelˡ-<; ≤-trans; <⇒≤; ≤-refl;
         _≟_; <-cmp; <-irrefl; ≰⇒>; m≤n⇒m<n∨m≡n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m;
         m+n∸m≡n; m+n≮m; +-identityʳ; +-suc; +-assoc; +-comm;
         ⊔-assoc; ⊔-comm; ⊔-identityʳ; ⊔-lub; m≤m⊔n;
         n≤1+n; suc-injective; m≤n⊔m)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Nullary using (Dec; yes; no; ¬_; ⌊_⌋)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂; cong; cong₂)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-rename-commute; rename-[]ᵗ-commute;
         rename-subst; rename-subst-commute; exts-sub-cons; cons-sub)
open import strong.Context
  using (TCtx; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld;
         skip-abst; skip-rvld; Ctx; _∋_⦂_; here; there; ⤊)
open import strong.Weakening using (wf-rename-fv; fv-scope; wf-⇑-abst)
open import strong.Boundary

private
  variable
    Δ : TCtx
    A A′ B C B₀ B₁ B₂ : Ty
    L L′ M M′ N N′ V W F : Term
    Θ : BCtx
    n x : ℕ

------------------------------------------------------------------------
-- Term-variable substitution (for Beta).  Identity on wrappers: a wrapped value
-- is term-closed (its body is typed at []), so no term variable reaches inside.
-- renameᵀ (type-variable renaming through a wrapper) is PROVISIONAL — the simple
-- Beta example below never pushes a wrapper under a Λ, so it isn't exercised; the
-- correct version is the next piece (needed for the general substitution lemma).
------------------------------------------------------------------------

extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renameᵀᵐ : (ℕ → ℕ) → Term → Term
renameᵀᵐ ρ (` x)          = ` (ρ x)
renameᵀᵐ ρ ($ n)          = $ n
renameᵀᵐ ρ (ƛ A ∙ N)      = ƛ A ∙ renameᵀᵐ (extⁿ ρ) N
renameᵀᵐ ρ (L · M)        = renameᵀᵐ ρ L · renameᵀᵐ ρ M
renameᵀᵐ ρ (Λ N)          = Λ (renameᵀᵐ ρ N)
renameᵀᵐ ρ (L ·[ B , A ]) = renameᵀᵐ ρ L ·[ B , A ]
renameᵀᵐ ρ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

-- Renaming a wrapper's type variables (ρ : Γ → Γ').  Reveal reps rename by ρ,
-- conceal indices by ρ; B₀ lives over the boundary frame (reveals ++ Γ) so it
-- renames by liftⁿ (revs Θ) ρ; the body and conceal reps live over the interior,
-- which renames by intRenᵇ — identity below a conceal that absorbs ρ (a conceal
-- restricts to Γ↓X, and restrictRen X ρ is the induced renaming on Γ↓X).
liftⁿ : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
liftⁿ zero    ρ = ρ
liftⁿ (suc r) ρ = extᵗ (liftⁿ r ρ)

restrictRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
restrictRen X ρ j = ρ (suc X + j) ∸ suc (ρ X)

-- interior renaming (whole-Γ): a SINGLE restriction at cmax (deepRen), lifted
-- past the reveal variables.  restrictRen c is the induced renaming on Γ↓c.
deepRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
deepRen zero    ρ = ρ
deepRen (suc c) ρ = restrictRen c ρ

intRen : (ℕ → ℕ) → BCtx → (ℕ → ℕ)
intRen ρ Θ = liftⁿ (revs Θ) (deepRen (cmax Θ) ρ)

renᴮ : (ℕ → ℕ) → (ℕ → ℕ) → BCtx → BCtx      -- ρ for reveal reps/indices, ir for conceal reps
renᴮ ρ ir []             = []
renᴮ ρ ir (rvl A   ∷ Θ) = rvl (renameᵗ ρ A)  ∷ renᴮ ρ ir Θ
renᴮ ρ ir (cnc X A ∷ Θ) = cnc (ρ X) (renameᵗ ir A) ∷ renᴮ ρ ir Θ

-- Shifting the conceal reps.  R1 (a boundary meets a type application)
-- grows the interior by ONE fresh abstract variable, so the conceal reps —
-- which live over the WHOLE interior — must be renamed by suc.  Reveal reps
-- are exterior and untouched, so neither face's reveal side moves.
shiftReps : BCtx → BCtx
shiftReps []             = []
shiftReps (rvl A   ∷ Θ) = rvl A ∷ shiftReps Θ
shiftReps (cnc X A ∷ Θ) = cnc X (renameᵗ suc A) ∷ shiftReps Θ

revs-shiftReps : ∀ Θ → revs (shiftReps Θ) ≡ revs Θ
revs-shiftReps []             = refl
revs-shiftReps (rvl A   ∷ Θ) = cong suc (revs-shiftReps Θ)
revs-shiftReps (cnc X A ∷ Θ) = revs-shiftReps Θ

cmax-shiftReps : ∀ Θ → cmax (shiftReps Θ) ≡ cmax Θ
cmax-shiftReps []             = refl
cmax-shiftReps (rvl A   ∷ Θ) = cmax-shiftReps Θ
cmax-shiftReps (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-shiftReps Θ)

-- the interior of the shifted boundary is the old one plus one abst
intOf-shift : ∀ (Γ : TCtx) A Θ
            → intOf Γ (rvl A ∷ shiftReps Θ) ≡ abst ∷ intOf Γ Θ
intOf-shift Γ A Θ rewrite revs-shiftReps Θ | cmax-shiftReps Θ = refl

------------------------------------------------------------------------
-- Dual boundary (R2).  Θᵈ = dualᵇ Θ turns the boundary inside out: its
-- exterior is intOf Δ Θ and its interior is (the rebuild of) Δ.  Every
-- REVEAL of Θ becomes a CONCEAL of Θᵈ at its interior index, keeping its
-- rep — a reveal rep is read in Δ, which is Θᵈ's interior, exactly a
-- conceal rep's home; every Δ-slot 0 … cmax Θ ∸ 1 that Θ dropped becomes a
-- REVEAL of Θᵈ whose rep is Θ's conceal rep for that slot (read in
-- intOf Δ Θ = Θᵈ's exterior).  A dropped slot that is NOT concealed is
-- BLOCKED; it gets an arbitrary rep (`ℕ), which is sound precisely because
-- (env)'s Scoped premise forbids B₀ from naming it — the exterior face law
-- fails exactly there (notes/BoundaryRules.md §2(a)).
------------------------------------------------------------------------

repOf : ℕ → BCtx → Ty            -- the rep Θ conceals slot i at (`ℕ if none)
repOf i []             = `ℕ
repOf i (rvl A   ∷ Θ) = repOf i Θ
repOf i (cnc X A ∷ Θ) with i ≟ X
repOf i (cnc X A ∷ Θ) | yes _ = A
repOf i (cnc X A ∷ Θ) | no  _ = repOf i Θ

rvlsOf : ℕ → ℕ → BCtx → BCtx     -- k reveals, for the dropped slots s, s+1, …
rvlsOf zero    s Θ = []
rvlsOf (suc k) s Θ = rvl (repOf s Θ) ∷ rvlsOf k (suc s) Θ

cncOfRevs : ℕ → BCtx → BCtx      -- conceal each reveal var, at j, j+1, …
cncOfRevs j []             = []
cncOfRevs j (rvl A   ∷ Θ) = cnc j A ∷ cncOfRevs (suc j) Θ
cncOfRevs j (cnc X A ∷ Θ) = cncOfRevs j Θ

dualᵇ : BCtx → BCtx
dualᵇ Θ = rvlsOf (cmax Θ) 0 Θ ++ cncOfRevs 0 Θ

-- The two boundary frames hold the same slots in a different order:
-- [reveals of Θ][dropped Δ-slots][kept Δ-slots] becomes
-- [dropped Δ-slots][reveals of Θ][kept Δ-slots], so a boundary type read
-- over Θ's frame is transported to Θᵈ's frame by this block swap.
swapIdx : ℕ → ℕ → ℕ → ℕ
swapIdx r c X with X <? r
swapIdx r c X | yes _ = c + X
swapIdx r c X | no  _ with (X ∸ r) <? c
swapIdx r c X | no _ | yes _ = X ∸ r
swapIdx r c X | no _ | no  _ = X

swapᵇ : BCtx → ℕ → ℕ
swapᵇ Θ = swapIdx (revs Θ) (cmax Θ)

renameᵀ : (ℕ → ℕ) → Term → Term          -- rename TYPE variables
renameᵀ ρ (` x)          = ` x
renameᵀ ρ ($ n)          = $ n
renameᵀ ρ (ƛ A ∙ N)      = ƛ (renameᵗ ρ A) ∙ renameᵀ ρ N
renameᵀ ρ (L · M)        = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)          = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (L ·[ B , A ]) = renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renameᵀ ρ (M ⟪ Θ , B₀ ⟫) =
  renameᵀ (intRen ρ Θ) M ⟪ renᴮ ρ (intRen ρ Θ) Θ , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫

⇑ᵀ : Term → Term
⇑ᵀ = renameᵀ suc

extsᵀᵐ : (ℕ → Term) → (ℕ → Term)
extsᵀᵐ σ zero    = ` zero
extsᵀᵐ σ (suc x) = renameᵀᵐ suc (σ x)

substᵀᵐ : (ℕ → Term) → Term → Term
substᵀᵐ σ (` x)          = σ x
substᵀᵐ σ ($ n)          = $ n
substᵀᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵀᵐ (extsᵀᵐ σ) N
substᵀᵐ σ (L · M)        = substᵀᵐ σ L · substᵀᵐ σ M
substᵀᵐ σ (Λ N)          = Λ (substᵀᵐ (λ x → ⇑ᵀ (σ x)) N)
substᵀᵐ σ (L ·[ B , A ]) = substᵀᵐ σ L ·[ B , A ]
substᵀᵐ σ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵀᵐ (λ { zero → W ; (suc x) → ` x }) N

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GVal : Term → Set
data Value : Term → Set

data GVal where
  G-ƛ : GVal (ƛ A ∙ N)
  G-Λ : Value V → GVal (Λ V)

data Value where
  V-$  : Value ($ n)
  V-G  : GVal V → Value V
  V-⟪⟫ : Value V → Value (V ⟪ Θ , B₀ ⟫)

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

infix 2 _-→_
data _-→_ : Term → Term → Set where

  -- TyBeta: a boundary is BORN.  The ∀-body B is recorded as the BOUNDARY type;
  -- internal type = B[γ] = B, external type = B[ρ] = B[A]ᵗ.
  TyBeta : Value V
      → (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫

  -- Beta
  Beta : Value W
      → (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- R1: a wrapped Λ meets a TYPE APPLICATION (the DIRECT-COMBINE form —
  -- notes/DECISIONS.md, Decision 2 as revised).  The elimination CONSUMES the
  -- Λ: the Λ-binder's slot IS the new reveal slot, so the type argument A is
  -- RECORDED as that reveal's rep — never pushed inward, which is what made
  -- the old design unsound (Example 8: A may name a variable the interior
  -- blocks).  There is NO ⇑ᵀ on the term (the design's no-term-shift
  -- principle: a shift forgets which variables a term may not mention); the
  -- CONCEAL REPS do shift, but they are types, and they must, since they live
  -- over the whole interior, which gains the Λ's abstract variable
  -- (shiftReps).  The redex's B is forced by the typing: (env) gives the
  -- wrapper's external face as `∀ (substᵗ (extsᵗ (ρᵇ Θ)) B₀).
  -- Partial by design: a wrapper-bodied wrapper at a ∀ face is a Merge redex
  -- (Decision 3), not a TyWrap redex.
  TyWrap : Value V
      → ((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  -- R2: a wrapped ƛ meets an APPLICATION.  Symmetric to TyWrap: the
  -- elimination CONSUMES the ƛ and β-substitutes in one step.  The argument
  -- lives in the EXTERIOR, so it is moved inside through the DUAL boundary
  -- (dualᵇ) first; _[_]ᵐ is TERM-variable substitution only, so again no term
  -- shift is involved.  B₁ is read over Θ's boundary frame, so the dual's
  -- boundary type is B₁ renamed by the frame permutation swapᵇ.  The dual's
  -- EXTERIOR face is then the argument type the ƛ demands and its INTERIOR
  -- face is W's type — but only at ACCESSIBLE slots (a blocked slot gets a
  -- dummy rep), which is why R2's preservation goes through subst-cong-sc
  -- with (env)'s scope premise for B₁.  Partial like TyWrap: a wrapper-bodied
  -- wrapper at a ⇒ face waits for Merge.
  Wrap : Value W
      → ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
        -→ (N [ W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ]ᵐ) ⟪ Θ , B₂ ⟫

  -- ξ (congruence): the evaluation frames, left-to-right call-by-value.
  -- ξ-Λ and ξ-⟪⟫ are not optional bookkeeping: Λ V is a value only when V is
  -- (G-Λ) and V ⟪ Θ , B₀ ⟫ only when V is (V-⟪⟫), so the body of a Λ and the
  -- interior of a boundary must be reduced in place before either is a value.
  ξ-·-l : L -→ L′
        → L · M -→ L′ · M

  ξ-·-r : Value V → M -→ M′
        → V · M -→ V · M′

  ξ-·[] : L -→ L′
        → L ·[ B , A ] -→ L′ ·[ B , A ]

  ξ-Λ   : N -→ N′
        → Λ N -→ Λ N′

  ξ-⟪⟫  : M -→ M′
        → M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- Worked example:  (ΛX. λx:X.x) [X→X, ℕ]  →  (λx:X.x)⟪↑X:=ℕ⟫   (both : ℕ→ℕ)
------------------------------------------------------------------------

⊢redex-Λ : [] ∣ [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢redex-Λ = ⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) wf-ℕ

_ : (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫
_ = TyBeta (V-G G-ƛ)

⊢contractum-Λ : [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢contractum-Λ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                    (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Beta:  (λx:ℕ. x) · 5  →  5    (both : ℕ)
------------------------------------------------------------------------

⊢redex-ƛ : [] ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) ⦂ `ℕ
⊢redex-ƛ = ⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$

_ : (ƛ `ℕ ∙ ` 0) · ($ 5) -→ $ 5
_ = Beta V-$

⊢contractum-ƛ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
⊢contractum-ƛ = ⊢$

------------------------------------------------------------------------
-- Worked example for ξ-⟪⟫:  reduce the INTERIOR of a reveal boundary.
--   ((λx:ℕ. x) · 5) ⟪ ↑X:=ℕ , B₀=ℕ ⟫  →  5 ⟪ ↑X:=ℕ , B₀=ℕ ⟫   (both : ℕ)
-- The interior context is  abst ∣ []  (one reveal, no conceal); B₀ = ℕ has
-- no free variable, so both faces are ℕ: the boundary is inert on the type.
------------------------------------------------------------------------

⊢redex-bnd : [] ∣ [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢redex-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ (⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$)

_ : ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
    -→ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
_ = ξ-⟪⟫ (Beta V-$)

⊢contractum-bnd : [] ∣ [] ⊢ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ ⊢$

------------------------------------------------------------------------
-- Worked example for TyWrap (R1), on the NEW-DESIGN ANALOGUE OF EXAMPLE 8.
-- Example 8 (notes/old/Scratch7-9) is the closed program whose 4th step made the
-- OLD design ill-typed: a value concealed on X (index 1) is TYPE-APPLIED to
-- the SHALLOWER Λ-bound Y (index 0), which the interior blocks.  Under the
-- combined boundary the same redex steps to a WELL-TYPED term, because Y is
-- recorded as a REVEAL rep (read in the exterior) instead of being pushed
-- into the interior.
--
--   ((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ , ∀(Z→Z) ⟫) ·[ Z→Z , Y ]    : Y→Y
--     →  (λz:Z. z) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫             : Y→Y
--
-- The Λ is consumed: its binder's slot becomes the reveal slot, whose rep is
-- the type argument Y.  Nothing moves in the term (no ⇑ᵀ).
--
-- Δ8/Θ8 (ASCII 8) are this example's own context and boundary — NOT Boundary's
-- Γ₈/Θ₈, which are a different (spurious-conceal) example.
------------------------------------------------------------------------

polyid : Term
polyid = Λ (ƛ ` 0 ∙ ` 0)

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

Δ8 : TCtx                       -- Y (Λ-bound, index 0), X (index 1)
Δ8 = abst ∷ abst ∷ []

Θ8 : BCtx                       -- conceal X (index 1), rep ℕ
Θ8 = cnc 1 `ℕ ∷ []

_ : intOf Δ8 Θ8 ≡ []
_ = refl

_ : baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []          -- Y is BLOCKED inside
_ = refl

⊢redex-R1 : Δ8 ∣ [] ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                      ⦂ (` 0 ⇒ ` 0)
⊢redex-R1 =
  ⊢·[] (env (bwf↓ (skip-abst here-abst) wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-abst)

-- polyid is Λ (ƛ ` 0 ∙ ` 0), so the rule's Value premise is the Λ-BODY's:
-- V-G G-ƛ, not the whole polyid's V-G (G-Λ …)
_ : (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
_ = TyWrap (V-G G-ƛ)

-- this is notes/BoundaryRulesProbe.agda §2's ⊢contractum-R1′ verbatim
⊢contractum-R1 :
  Δ8 ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1 =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Wrap (R2), on a MIXED boundary — one reveal AND one
-- conceal, the shape R1 produces (⊢contractum-R1 above), and the case a
-- "restrict R2 to cmax Θ = 0" design would not cover.
--
--   ((λz:Z. z) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z→Z ⟫) · 3                        : ℕ
--     →  (3 ⟪ dualᵇ Θm , X ⟫) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z ⟫                : ℕ
--
-- The ƛ is consumed and its body ` 0 is substituted for, so the contractum is
-- the dual-wrapped argument under the original boundary.
--
-- Exterior Δm = [Y , X]; the interior is [Z] and Y is BLOCKED there.  The
-- dual is [↑ℕ , ↑ℕ , ↓Z:=ℕ]: it reveals the two dropped Δm-slots (X at its
-- conceal rep ℕ, the blocked Y at the dummy rep ℕ) and conceals the reveal
-- variable Z at its rep.  swapᵇ Θm sends Θm's frame [Z , Y , X] slot 0 (Z)
-- to slot 2 of the dual's frame [X , Y , Z], so the dual's boundary type is
-- ` 2.
------------------------------------------------------------------------

Δm : TCtx                       -- Y (index 0), X (index 1)
Δm = abst ∷ abst ∷ []

Θm : BCtx                       -- reveal Z:=ℕ, conceal X (index 1)
Θm = rvl `ℕ ∷ cnc 1 `ℕ ∷ []

_ : intOf Δm Θm ≡ abst ∷ []
_ = refl

_ : baseS Θm Δm ≡ ok ∷ blk ∷ ok ∷ []          -- Y is blocked
_ = refl

_ : dualᵇ Θm ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

_ : intOf (intOf Δm Θm) (dualᵇ Θm) ≡ Δm       -- the dual's interior is Δm
_ = refl

_ : swapᵇ Θm 0 ≡ 2
_ = refl

⊢redex-R2m : Δm ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3) ⦂ `ℕ
⊢redex-R2m =
  ⊢· (env (bwf↑ wf-ℕ (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
          (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
          (⊢ƛ (wf-var here-abst) (⊢` here)))
     ⊢$

-- the ƛ's body is ` 0, so N [ … ]ᵐ IS the wrapped argument (definitionally)
_ : ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3)
    -→ (($ 3) ⟪ dualᵇ Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫
_ = Wrap V-$

⊢contractum-R2m :
  Δm ∣ [] ⊢ (($ 3) ⟪ dualᵇ Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫ ⦂ `ℕ
⊢contractum-R2m =
  env (bwf↑ wf-ℕ (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-var hereᵒ)
      (env (bwf↑ wf-ℕ (bwf↑ wf-ℕ (bwf↓ here-abst wf-ℕ bwf[])))
           (sc-var (thereᵒ (thereᵒ hereᵒ)))
           ⊢$)

------------------------------------------------------------------------
-- renameᵀ through a boundary, verified on ⇑ᵀ of the non-spurious ($7)⟪Θ₈, X⟫.
-- Under ⇑ᵀ (new abstract W at Γ-index 0):  conceal index 1 ↦ 2, reveal rep ` 0
-- (=Y) ↦ ` 1, B₀ = X = ` 2 ↦ ` 3 (bframe lift), body 7 unchanged (conceal absorbs
-- the shift, so intRenᵇ = id).
------------------------------------------------------------------------

_ : ⇑ᵀ (($ 7) ⟪ Θ₈ , ` 2 ⟫) ≡ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫
_ = refl

-- ⊢renameᵀ on this instance: the renamed wrapper types at abst ∷ Γ₈ with the
-- renamed external type ` 2 (= renameᵗ suc of the original external ` 1 = X).
_ : (abst ∷ Γ₈) ∣ [] ⊢ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫ ⦂ ` 2
_ = env (bwf↓ (skip-abst (skip-abst here-rvld)) wf-ℕ
             (bwf↑ (wf-var (skip-abst here-abst)) bwf[]))
        (sc-var (thereᵒ (thereᵒ (thereᵒ hereᵒ)))) ⊢$

------------------------------------------------------------------------
-- Type-variable renaming preserves typing  (⊢renameᵀ)
------------------------------------------------------------------------

∋-map : ∀ {ρ} {Γₜ : Ctx} {x A} → Γₜ ∋ x ⦂ A → map (renameᵗ ρ) Γₜ ∋ x ⦂ renameᵗ ρ A
∋-map here      = here
∋-map (there p) = there (∋-map p)

wf-ren : ∀ {ρ Δ Δ'} {A : Ty}
       → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Δ ⊢ A → Δ' ⊢ renameᵗ ρ A
wf-ren h wfA = wf-rename-fv (λ y → h (fv-scope wfA y)) wfA

ext-h : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
      → (∀ {X} → (abst ∷ Δ) ∋tv X → (abst ∷ Δ') ∋tv extᵗ ρ X)
ext-h h here-abst    = here-abst
ext-h h (skip-abst p) = skip-abst (h p)

⤊-ren : ∀ {ρ} (Γₜ : Ctx) → map (renameᵗ (extᵗ ρ)) (⤊ Γₜ) ≡ ⤊ (map (renameᵗ ρ) Γₜ)
⤊-ren []            = refl
⤊-ren {ρ} (A ∷ Γₜ) = cong₂ _∷_ pt (⤊-ren Γₜ)
  where pt : renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
        pt = trans (rename-rename-commute suc (extᵗ ρ) A)
                   (sym (rename-rename-commute ρ suc A))

-- ↓ / ∋tv bridge: a variable of the existential scope Δ↓X is variable suc X + Y
-- of Δ, and back.  (Needed for the interior commutation.)
↓-∋ : ∀ {Δ} X {Y} → (Δ ↓ X) ∋tv Y → Δ ∋tv (suc X + Y)
↓-∋ {[]}        X       ()
↓-∋ {abst   ∷ Δ} zero    p = skip-abst p
↓-∋ {rvld A ∷ Δ} zero    p = skip-rvld p
↓-∋ {abst   ∷ Δ} (suc X) p = skip-abst (↓-∋ X p)
↓-∋ {rvld A ∷ Δ} (suc X) p = skip-rvld (↓-∋ X p)

↓-∋⁻ : ∀ {Δ} X {Z} → Δ ∋tv (suc X + Z) → (Δ ↓ X) ∋tv Z
↓-∋⁻ {[]}        X       ()
↓-∋⁻ {abst   ∷ Δ} zero    (skip-abst p) = p
↓-∋⁻ {rvld A ∷ Δ} zero    (skip-rvld p) = p
↓-∋⁻ {abst   ∷ Δ} (suc X) (skip-abst p) = ↓-∋⁻ X p
↓-∋⁻ {rvld A ∷ Δ} (suc X) (skip-rvld p) = ↓-∋⁻ X p

-- Mono = strictly monotone renaming (the shape of every renaming that arises:
-- weakenings and their lifts).  restrictRen preserves it.
Mono : (ℕ → ℕ) → Set
Mono ρ = ∀ {a b} → a < b → ρ a < ρ b

-- extᵗ preserves monotonicity, so ⊢renameᵀ can recurse under a Λ.
Mono-extᵗ : ∀ {ρ} → Mono ρ → Mono (extᵗ ρ)
Mono-extᵗ mono {zero}  {suc _} _         = s≤s z≤n
Mono-extᵗ mono {suc _} {suc _} (s≤s a<b) = s≤s (mono a<b)

∸-strict : ∀ {c p q} → c ≤ p → p < q → (p ∸ c) < (q ∸ c)
∸-strict {c} {p} {q} c≤p p<q =
  +-cancelˡ-< c _ _
    (subst₂ _<_ (sym (m+[n∸m]≡n c≤p)) (sym (m+[n∸m]≡n c≤q)) p<q)
  where c≤q : c ≤ q
        c≤q = ≤-trans c≤p (<⇒≤ p<q)

-- external commutation: renaming commutes with the external projection ρᵇ.
ρᵇ-comm : ∀ ρ ir Θ X
        → ρᵇ (renᴮ ρ ir Θ) (liftⁿ (revs Θ) ρ X) ≡ renameᵗ ρ (ρᵇ Θ X)
ρᵇ-comm ρ ir []            X       = refl
ρᵇ-comm ρ ir (rvl A   ∷ Θ) zero    = refl
ρᵇ-comm ρ ir (rvl A   ∷ Θ) (suc Y) = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (cnc X A ∷ Θ) Y       = ρᵇ-comm ρ ir Θ Y

C-ext : ∀ ρ ir Θ B₀
      → substᵗ (ρᵇ (renᴮ ρ ir Θ)) (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ ρ (substᵗ (ρᵇ Θ) B₀)
C-ext ρ ir Θ B₀ =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ) (ρᵇ (renᴮ ρ ir Θ)) B₀)
    (trans (subst-cong (ρᵇ-comm ρ ir Θ) B₀)
           (sym (rename-subst ρ (ρᵇ Θ) B₀)))

-- lookup preservation through one restriction Δ↓X (needed for the interior)
h-restrict : ∀ {ρ Δ Δ'} X
  → (∀ {Y} → Δ ∋tv Y → Δ' ∋tv ρ Y) → Mono ρ
  → ∀ {Y} → (Δ ↓ X) ∋tv Y → (Δ' ↓ ρ X) ∋tv restrictRen X ρ Y
h-restrict {ρ} X h mono {Y} p =
  ↓-∋⁻ (ρ X) (subst (λ n → _ ∋tv n) eq (h (↓-∋ X p)))
  where
    lt : suc (ρ X) ≤ ρ (suc X + Y)
    lt = mono (m≤m+n (suc X) Y)
    eq : ρ (suc X + Y) ≡ suc (ρ X) + restrictRen X ρ Y
    eq = sym (m+[n∸m]≡n lt)

------------------------------------------------------------------------
-- Monotonicity toolbox.  Mono is injective, and it survives every
-- combinator the interior renaming intRen is built from.
------------------------------------------------------------------------

Mono→inj : ∀ {ρ} → Mono ρ → ∀ {a b} → ρ a ≡ ρ b → a ≡ b
Mono→inj {ρ} mono {a} {b} eq with <-cmp a b
Mono→inj {ρ} mono {a} {b} eq | tri< a<b _ _ =
  ⊥-elim (<-irrefl eq (mono a<b))
Mono→inj {ρ} mono {a} {b} eq | tri≈ _ a≡b _ = a≡b
Mono→inj {ρ} mono {a} {b} eq | tri> _ _ b<a =
  ⊥-elim (<-irrefl (sym eq) (mono b<a))

Mono→≤ : ∀ {ρ} → Mono ρ → ∀ {a b} → a ≤ b → ρ a ≤ ρ b
Mono→≤ mono a≤b with m≤n⇒m<n∨m≡n a≤b
Mono→≤ mono a≤b | inj₁ a<b  = <⇒≤ (mono a<b)
Mono→≤ mono a≤b | inj₂ refl = ≤-refl

Mono-restrictRen : ∀ {ρ} X → Mono ρ → Mono (restrictRen X ρ)
Mono-restrictRen {ρ} X mono {a} {b} a<b =
  ∸-strict (mono (m≤m+n (suc X) a)) (mono (+-monoʳ-< (suc X) a<b))

Mono-deepRen : ∀ {ρ} c → Mono ρ → Mono (deepRen c ρ)
Mono-deepRen zero    mono = mono
Mono-deepRen (suc c) mono = Mono-restrictRen c mono

Mono-liftⁿ : ∀ {ρ} r → Mono ρ → Mono (liftⁿ r ρ)
Mono-liftⁿ zero    mono = mono
Mono-liftⁿ (suc r) mono = Mono-extᵗ (Mono-liftⁿ r mono)

Mono-intRen : ∀ {ρ} Θ → Mono ρ → Mono (intRen ρ Θ)
Mono-intRen Θ mono = Mono-liftⁿ (revs Θ) (Mono-deepRen (cmax Θ) mono)

------------------------------------------------------------------------
-- renᴮ keeps the reveal count, and (for a Mono ρ) sends the deepest
-- conceal index X to ρ X — so cmax has one of two shapes after renaming.
------------------------------------------------------------------------

revs-ren : ∀ ρ ir Θ → revs (renᴮ ρ ir Θ) ≡ revs Θ
revs-ren ρ ir []            = refl
revs-ren ρ ir (rvl A ∷ Θ)   = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (cnc X A ∷ Θ) = revs-ren ρ ir Θ

⊔-mono-comm : ∀ {ρ} → Mono ρ → ∀ a b → ρ (a ⊔ b) ≡ ρ a ⊔ ρ b
⊔-mono-comm {ρ} mono a b with a ≤? b
⊔-mono-comm {ρ} mono a b | yes a≤b =
  trans (cong ρ (m≤n⇒m⊔n≡n a≤b)) (sym (m≤n⇒m⊔n≡n (Mono→≤ mono a≤b)))
⊔-mono-comm {ρ} mono a b | no ¬a≤b =
  trans (cong ρ (m≥n⇒m⊔n≡m b≤a)) (sym (m≥n⇒m⊔n≡m (Mono→≤ mono b≤a)))
  where b≤a : b ≤ a
        b≤a = <⇒≤ (≰⇒> ¬a≤b)

-- the two possible shapes of cmax under renaming
data CmaxV (ρ ir : ℕ → ℕ) (Θ : BCtx) : Set where
  cm-0 : cmax Θ ≡ 0 → cmax (renᴮ ρ ir Θ) ≡ 0 → CmaxV ρ ir Θ
  cm-s : ∀ X → cmax Θ ≡ suc X → cmax (renᴮ ρ ir Θ) ≡ suc (ρ X)
       → CmaxV ρ ir Θ

cmax-ren : ∀ {ρ} → Mono ρ → ∀ ir Θ → CmaxV ρ ir Θ
cmax-ren mono ir [] = cm-0 refl refl
cmax-ren mono ir (rvl A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren mono ir (rvl A ∷ Θ) | cm-0 e e'   = cm-0 e e'
cmax-ren mono ir (rvl A ∷ Θ) | cm-s Y e e' = cm-s Y e e'
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-0 e e' =
  cm-s X (cong (λ n → suc X ⊔ n) e) (cong (λ n → suc (ρ X) ⊔ n) e')
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-s Y e e' =
  cm-s (X ⊔ Y) (cong (λ n → suc X ⊔ n) e)
       (trans (cong (λ n → suc (ρ X) ⊔ n) e')
              (cong suc (sym (⊔-mono-comm mono X Y))))

------------------------------------------------------------------------
-- liftⁿ / prepId below and above the reveal prefix, and the view that
-- splits a boundary-frame index into "reveal prefix" or "deep".
------------------------------------------------------------------------

liftⁿ-lo : ∀ r ρ X → X < r → liftⁿ r ρ X ≡ X
liftⁿ-lo zero    ρ X       ()
liftⁿ-lo (suc r) ρ zero    _         = refl
liftⁿ-lo (suc r) ρ (suc X) (s≤s X<r) = cong suc (liftⁿ-lo r ρ X X<r)

liftⁿ-hi : ∀ r ρ i → liftⁿ r ρ (r + i) ≡ r + ρ i
liftⁿ-hi zero    ρ i = refl
liftⁿ-hi (suc r) ρ i = cong suc (liftⁿ-hi r ρ i)

prepId-lo : ∀ r (σ : Substᵗ) X → X < r → prepId r σ X ≡ ` X
prepId-lo r σ X X<r with X <? r
prepId-lo r σ X X<r | yes _   = refl
prepId-lo r σ X X<r | no ¬X<r = ⊥-elim (¬X<r X<r)

prepId-hi : ∀ r (σ : Substᵗ) i → prepId r σ (r + i) ≡ σ i
prepId-hi r σ i with (r + i) <? r
prepId-hi r σ i | yes lt = ⊥-elim (m+n≮m r i lt)
prepId-hi r σ i | no  _  = cong σ (m+n∸m≡n r i)

-- prepId-hi with the reveal count supplied up to an equation (needed
-- because γᵇ of a renamed boundary mentions revs (renᴮ …), not revs Θ)
prepId-hi′ : ∀ r r' (σ : Substᵗ) i → r' ≡ r → prepId r' σ (r + i) ≡ σ i
prepId-hi′ r .r σ i refl = prepId-hi r σ i

split : ∀ r X → (X < r) ⊎ (Σ ℕ λ i → X ≡ r + i)
split zero    X       = inj₂ (X , refl)
split (suc r) zero    = inj₁ (s≤s z≤n)
split (suc r) (suc X) with split r X
split (suc r) (suc X) | inj₁ X<r        = inj₁ (s≤s X<r)
split (suc r) (suc X) | inj₂ (i , X≡ri) = inj₂ (i , cong suc X≡ri)

------------------------------------------------------------------------
-- Decidable/Bool plumbing for isConc (whose cons case is ⌊ i ≟ X ⌋ ∨ …).
------------------------------------------------------------------------

⌊⌋-true : ∀ {P : Set} (d : Dec P) → ⌊ d ⌋ ≡ true → P
⌊⌋-true (yes p) _  = p
⌊⌋-true (no ¬p) ()

⌊⌋-of : ∀ {P : Set} (d : Dec P) → P → ⌊ d ⌋ ≡ true
⌊⌋-of (yes _) _ = refl
⌊⌋-of (no ¬p) p = ⊥-elim (¬p p)

∨-true : ∀ (b₁ b₂ : Bool) → (b₁ ∨ b₂) ≡ true → (b₁ ≡ true) ⊎ (b₂ ≡ true)
∨-true true  b₂ e = inj₁ refl
∨-true false b₂ e = inj₂ e

isConc-cons : ∀ i X A Θ → isConc i (cnc X A ∷ Θ) ≡ true
            → (i ≡ X) ⊎ (isConc i Θ ≡ true)
isConc-cons i X A Θ c with ∨-true ⌊ i ≟ X ⌋ (isConc i Θ) c
isConc-cons i X A Θ c | inj₁ t = inj₁ (⌊⌋-true (i ≟ X) t)
isConc-cons i X A Θ c | inj₂ t = inj₂ t

isConc-here : ∀ i X A Θ → i ≡ X → isConc i (cnc X A ∷ Θ) ≡ true
isConc-here i X A Θ p = cong (λ b → b ∨ isConc i Θ) (⌊⌋-of (i ≟ X) p)

isConc-there : ∀ i X A Θ → isConc i Θ ≡ true → isConc i (cnc X A ∷ Θ) ≡ true
isConc-there i X A Θ c =
  trans (cong (λ b → ⌊ i ≟ X ⌋ ∨ b) c) (∨-zeroʳ ⌊ i ≟ X ⌋)

-- a concealed index stays concealed after renaming (indices move by ρ)
isConc-ren : ∀ ρ ir Θ i → isConc i Θ ≡ true
           → isConc (ρ i) (renᴮ ρ ir Θ) ≡ true
isConc-ren ρ ir []            i ()
isConc-ren ρ ir (rvl A ∷ Θ)   i c = isConc-ren ρ ir Θ i c
isConc-ren ρ ir (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₁ p =
  isConc-here (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) (cong ρ p)
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ)
               (isConc-ren ρ ir Θ i t)

------------------------------------------------------------------------
-- The accessibility bridge: baseS Θ Δ ∋ok (revs Θ + i) says exactly that
-- i is a KEPT (cmax Θ ≤ i) or CONCEALED index of Δ — the two cases where
-- γcnc commutes with renaming.  Both directions are needed.
------------------------------------------------------------------------

ok≢blk : ok ≡ blk → ⊥
ok≢blk ()

∋ok-head : ∀ {s Ψ} → (s ∷ Ψ) ∋ok zero → s ≡ ok
∋ok-head hereᵒ = refl

∋ok-tail : ∀ {s Ψ j} → (s ∷ Ψ) ∋ok suc j → Ψ ∋ok j
∋ok-tail (thereᵒ p) = p

∋ok-≡ : ∀ {Ψ X X'} → X ≡ X' → Ψ ∋ok X → Ψ ∋ok X'
∋ok-≡ refl p = p

∋tv-tail : ∀ {E Γ j} → (E ∷ Γ) ∋tv suc j → Γ ∋tv j
∋tv-tail (skip-abst p) = p
∋tv-tail (skip-rvld p) = p

repl-drop : ∀ r {Ψ i} → (repl-ok r ++ Ψ) ∋ok (r + i) → Ψ ∋ok i
repl-drop zero    p = p
repl-drop (suc r) p = repl-drop r (∋ok-tail p)

repl-add : ∀ r {Ψ i} → Ψ ∋ok i → (repl-ok r ++ Ψ) ∋ok (r + i)
repl-add zero    p = p
repl-add (suc r) p = thereᵒ (repl-add r p)

repl-lo : ∀ r {Ψ} X → X < r → (repl-ok r ++ Ψ) ∋ok X
repl-lo zero    X       ()
repl-lo (suc r) zero    _         = hereᵒ
repl-lo (suc r) (suc X) (s≤s X<r) = thereᵒ (repl-lo r X X<r)

slotsᴳ-ok : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → slotAt Θ (k + j) ≡ ok
slotsᴳ-ok Θ []      k j ()
slotsᴳ-ok Θ (E ∷ Γ) k zero    p rewrite +-identityʳ k = ∋ok-head p
slotsᴳ-ok Θ (E ∷ Γ) k (suc j) p rewrite +-suc k j =
  slotsᴳ-ok Θ Γ (suc k) j (∋ok-tail p)

slotsᴳ-∋tv : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → Γ ∋tv j
slotsᴳ-∋tv Θ []            k j       ()
slotsᴳ-∋tv Θ (abst ∷ Γ)    k zero    p = here-abst
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k zero    p = here-rvld
slotsᴳ-∋tv Θ (abst ∷ Γ)    k (suc j) p =
  skip-abst (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k (suc j) p =
  skip-rvld (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))

slotsᴳ-add : ∀ Θ Γ k j → Γ ∋tv j → slotAt Θ (k + j) ≡ ok
           → slotsᴳ Θ k Γ ∋ok j
slotsᴳ-add Θ []      k j       ()  e
slotsᴳ-add Θ (E ∷ Γ) k zero    q   e =
  subst (λ s → (s ∷ slotsᴳ Θ (suc k) Γ) ∋ok zero)
        (sym (trans (cong (slotAt Θ) (sym (+-identityʳ k))) e)) hereᵒ
slotsᴳ-add Θ (E ∷ Γ) k (suc j) q   e =
  thereᵒ (slotsᴳ-add Θ Γ (suc k) j (∋tv-tail q)
                     (trans (cong (slotAt Θ) (sym (+-suc k j))) e))

if-ok : ∀ (b : Bool) → b ≡ true → (if b then ok else blk) ≡ ok
if-ok true  _  = refl
if-ok false ()

if-acc : ∀ (b : Bool) → (b ≡ true) ⊎ ((if b then ok else blk) ≡ blk)
if-acc true  = inj₁ refl
if-acc false = inj₂ refl

slotAt-acc : ∀ Θ i
  → (cmax Θ ≤ i) ⊎ ((isConc i Θ ≡ true) ⊎ (slotAt Θ i ≡ blk))
slotAt-acc Θ i with cmax Θ ≤? i
slotAt-acc Θ i | yes le = inj₁ le
slotAt-acc Θ i | no ¬le with if-acc (isConc i Θ)
slotAt-acc Θ i | no ¬le | inj₁ c = inj₂ (inj₁ c)
slotAt-acc Θ i | no ¬le | inj₂ b = inj₂ (inj₂ b)

acc-of : ∀ Θ i → slotAt Θ i ≡ ok → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
acc-of Θ i e with slotAt-acc Θ i
acc-of Θ i e | inj₁ le         = inj₁ le
acc-of Θ i e | inj₂ (inj₁ c)   = inj₂ c
acc-of Θ i e | inj₂ (inj₂ bk)  = ⊥-elim (ok≢blk (trans (sym e) bk))

slotAt-hi : ∀ Θ i → cmax Θ ≤ i → slotAt Θ i ≡ ok
slotAt-hi Θ i le with cmax Θ ≤? i
slotAt-hi Θ i le | yes _   = refl
slotAt-hi Θ i le | no ¬le  = ⊥-elim (¬le le)

slotAt-conc : ∀ Θ i → isConc i Θ ≡ true → slotAt Θ i ≡ ok
slotAt-conc Θ i c with cmax Θ ≤? i
slotAt-conc Θ i c | yes _  = refl
slotAt-conc Θ i c | no ¬le = if-ok (isConc i Θ) c

acc-slotAt : ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → slotAt Θ i ≡ ok
acc-slotAt Θ i (inj₁ le) = slotAt-hi Θ i le
acc-slotAt Θ i (inj₂ c)  = slotAt-conc Θ i c

baseS-acc : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i)
          → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
baseS-acc {Δ} Θ i p =
  acc-of Θ i (slotsᴳ-ok Θ Δ 0 i (repl-drop (revs Θ) p))

baseS-∋tv : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i) → Δ ∋tv i
baseS-∋tv {Δ} Θ i p = slotsᴳ-∋tv Θ Δ 0 i (repl-drop (revs Θ) p)

baseS-ok : ∀ {Δ} Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → Δ ∋tv i
         → baseS Θ Δ ∋ok (revs Θ + i)
baseS-ok {Δ} Θ i acc q =
  repl-add (revs Θ) (slotsᴳ-add Θ Δ 0 i q (acc-slotAt Θ i acc))

------------------------------------------------------------------------
-- Internal commutation.  The deep part of γᵇ is γcnc, which commutes
-- with ρ at kept and concealed indices (it does NOT at blocked ones —
-- that is exactly what the (env) scope premise rules out).
------------------------------------------------------------------------

-- the arithmetic side condition γcnc-comm needs at a kept index: with no
-- conceals ρ passes through, otherwise both sides restrict at the deepest
-- conceal (cmax Θ = suc X on the left, cmax Θ' = suc (ρ X) on the right).
deep-eq : ∀ {ρ} m m' → m ≡ 0 → m' ≡ 0 → ∀ j → m ≤ j
        → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq {ρ} m m' e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
        (cong (λ n → deepRen n ρ (j ∸ n)) (sym e))

deep-eq-s : ∀ {ρ} m m' X → m ≡ suc X → m' ≡ suc (ρ X) → ∀ j → m ≤ j
          → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq-s {ρ} m m' X e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
    (trans (cong (λ n → ρ n ∸ suc (ρ X)) (sym (m+[n∸m]≡n le')))
           (cong (λ n → deepRen n ρ (j ∸ n)) (sym e)))
  where le' : suc X ≤ j
        le' = subst (λ n → n ≤ j) e le

deep-hyp : ∀ {ρ} → Mono ρ → ∀ Θ j → cmax Θ ≤ j
  → ρ j ∸ cmax (renᴮ ρ (intRen ρ Θ) Θ)
    ≡ deepRen (cmax Θ) ρ (j ∸ cmax Θ)
deep-hyp {ρ} mono Θ j le with cmax-ren mono (intRen ρ Θ) Θ
deep-hyp {ρ} mono Θ j le | cm-0 e e'   = deep-eq (cmax Θ) _ e e' j le
deep-hyp {ρ} mono Θ j le | cm-s X e e' = deep-eq-s (cmax Θ) _ X e e' j le

acc-tail : ∀ m i X A Θ → ¬ (X ≡ i)
  → (m ≤ i) ⊎ (isConc i (cnc X A ∷ Θ) ≡ true)
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
acc-tail m i X A Θ ne (inj₁ le) = inj₁ le
acc-tail m i X A Θ ne (inj₂ c) with isConc-cons i X A Θ c
acc-tail m i X A Θ ne (inj₂ c) | inj₁ p = ⊥-elim (ne (sym p))
acc-tail m i X A Θ ne (inj₂ c) | inj₂ t = inj₂ t

γcnc-comm : ∀ {ρ} → Mono ρ → ∀ r m m' Θ i
  → (∀ j → m ≤ j → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m))
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
  → γcnc r m' (renᴮ ρ (liftⁿ r (deepRen m ρ)) Θ) (ρ i)
    ≡ renameᵗ (liftⁿ r (deepRen m ρ)) (γcnc r m Θ i)
γcnc-comm {ρ} mono r m m' [] i hyp (inj₁ le) =
  trans (cong (λ n → ` (r + n)) (hyp i le))
        (cong `_ (sym (liftⁿ-hi r (deepRen m ρ) (i ∸ m))))
γcnc-comm {ρ} mono r m m' [] i hyp (inj₂ ())
γcnc-comm {ρ} mono r m m' (rvl A ∷ Θ) i hyp acc =
  γcnc-comm mono r m m' Θ i hyp acc
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  with X ≟ i | ρ X ≟ ρ i
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes refl | yes _ = refl
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes p | no ¬q = ⊥-elim (¬q (cong ρ p))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | yes q = ⊥-elim (¬p (Mono→inj mono q))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | no ¬q =
  γcnc-comm mono r m m' Θ i hyp (acc-tail m i X A Θ ¬p acc)

-- γᵇ commutes with renaming at every ACCESSIBLE boundary-frame slot.
γᵇ-comm-lo : ∀ {ρ} → Mono ρ → ∀ Θ X → X < revs Θ
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-lo {ρ} mono Θ X lt =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-lo (revs Θ) ρ X lt))
    (trans (prepId-lo (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ X lt')
      (trans (cong `_ (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) X lt)))
             (cong (renameᵗ (intRen ρ Θ))
                   (sym (prepId-lo (revs Θ) _ X lt)))))
  where lt' : X < revs (renᴮ ρ (intRen ρ Θ) Θ)
        lt' = subst (λ n → X < n) (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt

γᵇ-comm-hi : ∀ {ρ Δ} → Mono ρ → ∀ Θ i
  → baseS Θ Δ ∋ok (revs Θ + i)
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ (revs Θ + i))
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ (revs Θ + i))
γᵇ-comm-hi {ρ} mono Θ i okp =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-hi (revs Θ) ρ i))
    (trans (prepId-hi′ (revs Θ) (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ (ρ i) rr)
      (trans (cong (λ n → γcnc n (cmax (renᴮ ρ (intRen ρ Θ) Θ))
                                 (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)) rr)
        (trans (γcnc-comm mono (revs Θ) (cmax Θ)
                          (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Θ i
                          (deep-hyp mono Θ) (baseS-acc Θ i okp))
               (cong (renameᵗ (intRen ρ Θ))
                     (sym (prepId-hi (revs Θ) _ i))))))
  where rr : revs (renᴮ ρ (intRen ρ Θ) Θ) ≡ revs Θ
        rr = revs-ren ρ (intRen ρ Θ) Θ

γᵇ-comm-ok : ∀ {ρ Δ} → Mono ρ → ∀ Θ X → baseS Θ Δ ∋ok X
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-ok mono Θ X okp with split (revs Θ) X
γᵇ-comm-ok mono Θ X okp | inj₁ lt = γᵇ-comm-lo mono Θ X lt
γᵇ-comm-ok mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  γᵇ-comm-hi mono Θ i okp

-- internal face: mirrors C-ext, but only at accessible slots (subst-cong-sc)
C-int : ∀ {ρ Δ B₀} → Mono ρ → ∀ Θ → Scoped (baseS Θ Δ) B₀
      → substᵗ (γᵇ (renᴮ ρ (intRen ρ Θ) Θ))
               (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ (intRen ρ Θ) (substᵗ (γᵇ Θ) B₀)
C-int {ρ} {Δ} {B₀} mono Θ sc =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ)
                              (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) B₀)
    (trans (subst-cong-sc sc (λ X okp → γᵇ-comm-ok mono Θ X okp))
           (sym (rename-subst (intRen ρ Θ) (γᵇ Θ) B₀)))

------------------------------------------------------------------------
-- The interior context transports: intOf Δ Θ → intOf Δ' (renᴮ … Θ).
------------------------------------------------------------------------

∋tv-≡ : ∀ {Γ Γ' Z Z'} → Γ ≡ Γ' → Z ≡ Z' → Γ ∋tv Z → Γ' ∋tv Z'
∋tv-≡ refl refl p = p

prepAbst-lo : ∀ r Γ Y → Y < r → prepAbst r Γ ∋tv Y
prepAbst-lo zero    Γ Y       ()
prepAbst-lo (suc r) Γ zero    _         = here-abst
prepAbst-lo (suc r) Γ (suc Y) (s≤s Y<r) =
  skip-abst (prepAbst-lo r Γ Y Y<r)

prepAbst-hi : ∀ r Γ Z → Γ ∋tv Z → prepAbst r Γ ∋tv (r + Z)
prepAbst-hi zero    Γ Z p = p
prepAbst-hi (suc r) Γ Z p = skip-abst (prepAbst-hi r Γ Z p)

prepAbst-hi⁻ : ∀ r Γ Z → prepAbst r Γ ∋tv (r + Z) → Γ ∋tv Z
prepAbst-hi⁻ zero    Γ Z p             = p
prepAbst-hi⁻ (suc r) Γ Z (skip-abst p) = prepAbst-hi⁻ r Γ Z p

-- dropN (suc X) is the existential prefix Δ ↓ X (the conceal interior)
dropN-↓ : ∀ (Γ : TCtx) X → dropN (suc X) Γ ≡ Γ ↓ X
dropN-↓ []             X       = refl
dropN-↓ (abst ∷ Γ)     zero    = refl
dropN-↓ (rvld A ∷ Γ)   zero    = refl
dropN-↓ (abst ∷ Γ)     (suc X) = dropN-↓ Γ X
dropN-↓ (rvld A ∷ Γ)   (suc X) = dropN-↓ Γ X

drop-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Z}
  → dropN (cmax Θ) Δ ∋tv Z
  → dropN (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Δ' ∋tv deepRen (cmax Θ) ρ Z
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q with cmax-ren mono (intRen ρ Θ) Θ
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-0 e e' =
  ∋tv-≡ (cong (λ n → dropN n Δ') (sym e'))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h (∋tv-≡ (cong (λ n → dropN n Δ) e) refl q))
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-s X e e' =
  ∋tv-≡ (trans (sym (dropN-↓ Δ' (ρ X)))
               (cong (λ n → dropN n Δ') (sym e')))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h-restrict X h mono
          (∋tv-≡ (trans (cong (λ n → dropN n Δ) e) (dropN-↓ Δ X)) refl q))

h-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Y}
  → intOf Δ Θ ∋tv Y
  → intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋tv intRen ρ Θ Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p with split (revs Θ) Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₁ lt =
  ∋tv-≡ (cong (λ n → prepAbst n (dropN (cmax Θ') Δ'))
              (sym (revs-ren ρ (intRen ρ Θ) Θ)))
        (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
        (prepAbst-lo (revs Θ) (dropN (cmax Θ') Δ') Y lt)
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₂ (Z , refl) =
  ∋tv-≡ (cong (λ n → prepAbst n (dropN (cmax Θ') Δ'))
              (sym (revs-ren ρ (intRen ρ Θ) Θ)))
        (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z))
        (prepAbst-hi (revs Θ) (dropN (cmax Θ') Δ')
                     (deepRen (cmax Θ) ρ Z)
                     (drop-int h mono Θ
                       (prepAbst-hi⁻ (revs Θ) (dropN (cmax Θ) Δ) Z p)))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ

------------------------------------------------------------------------
-- Boundary well-formedness and the (env) scope premise transport.
------------------------------------------------------------------------

bwf-ren : ∀ {ρ ir Δ Δ' Ψ Ψ' Θ}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
  → (∀ {Y} → Ψ ∋tv Y → Ψ' ∋tv ir Y)
  → Δ ∣ Ψ ⊢ᵇ Θ → Δ' ∣ Ψ' ⊢ᵇ renᴮ ρ ir Θ
bwf-ren h hi bwf[]           = bwf[]
bwf-ren h hi (bwf↑ wfA b)    = bwf↑ (wf-ren h wfA) (bwf-ren h hi b)
bwf-ren h hi (bwf↓ p wfA b)  =
  bwf↓ (h p) (wf-ren hi wfA) (bwf-ren h hi b)

sc-rename : ∀ {Ψ Ψ' ρ₀ A} → (∀ X → Ψ ∋ok X → Ψ' ∋ok ρ₀ X)
          → Scoped Ψ A → Scoped Ψ' (renameᵗ ρ₀ A)
sc-rename t (sc-var p)   = sc-var (t _ p)
sc-rename t sc-ℕ         = sc-ℕ
sc-rename t sc-𝔹         = sc-𝔹
sc-rename t (sc-⇒ sA sB) = sc-⇒ (sc-rename t sA) (sc-rename t sB)
sc-rename {Ψ} {Ψ'} {ρ₀} t (sc-∀ sA) = sc-∀ (sc-rename t-ext sA)
  where t-ext : ∀ X → (ok ∷ Ψ) ∋ok X → (ok ∷ Ψ') ∋ok extᵗ ρ₀ X
        t-ext zero    hereᵒ      = hereᵒ
        t-ext (suc X) (thereᵒ p) = thereᵒ (t X p)

-- a kept index stays kept and a concealed one stays concealed under ρ
acc-ren : ∀ {ρ} → Mono ρ → ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
  → (cmax (renᴮ ρ (intRen ρ Θ) Θ) ≤ ρ i)
    ⊎ (isConc (ρ i) (renᴮ ρ (intRen ρ Θ) Θ) ≡ true)
acc-ren {ρ} mono Θ i (inj₁ le) with cmax-ren mono (intRen ρ Θ) Θ
acc-ren {ρ} mono Θ i (inj₁ le) | cm-0 e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e') z≤n)
acc-ren {ρ} mono Θ i (inj₁ le) | cm-s X e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e')
              (mono (subst (λ n → n ≤ i) e le)))
acc-ren {ρ} mono Θ i (inj₂ c) =
  inj₂ (isConc-ren ρ (intRen ρ Θ) Θ i c)

baseS-ren : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → ∀ X → baseS Θ Δ ∋ok X
  → baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ' ∋ok liftⁿ (revs Θ) ρ X
baseS-ren {ρ} h mono Θ X okp with split (revs Θ) X
baseS-ren {ρ} h mono Θ X okp | inj₁ lt =
  ∋ok-≡ (sym (liftⁿ-lo (revs Θ) ρ X lt))
        (repl-lo (revs (renᴮ ρ (intRen ρ Θ) Θ)) X
                 (subst (λ n → X < n)
                        (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt))
baseS-ren {ρ} h mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  ∋ok-≡ (trans (cong (λ n → n + ρ i) (revs-ren ρ (intRen ρ Θ) Θ))
               (sym (liftⁿ-hi (revs Θ) ρ i)))
        (baseS-ok (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)
                  (acc-ren mono Θ i (baseS-acc Θ i okp))
                  (h (baseS-∋tv Θ i okp)))

sc-ren : ∀ {ρ Δ Δ' B₀} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → Scoped (baseS Θ Δ) B₀
  → Scoped (baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ')
           (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
sc-ren h mono Θ sc = sc-rename (baseS-ren h mono Θ) sc

-- ρ must be MONOTONE, not merely lookup-preserving: boundary renaming depends on
-- index order through cmax / restrictRen (a non-monotone ρ that permutes indices
-- could shrink a conceal's interior and strand a variable).
⊢renameᵀ : ∀ {ρ Δ Δ' Γₜ M A}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
⊢renameᵀ h mono (⊢` p)       = ⊢` (∋-map p)
⊢renameᵀ h mono ⊢$           = ⊢$
⊢renameᵀ h mono (⊢ƛ wfA ⊢N)  = ⊢ƛ (wf-ren h wfA) (⊢renameᵀ h mono ⊢N)
⊢renameᵀ h mono (⊢· ⊢L ⊢M)   = ⊢· (⊢renameᵀ h mono ⊢L) (⊢renameᵀ h mono ⊢M)
⊢renameᵀ h mono (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Γ' → _ ∣ Γ' ⊢ _ ⦂ _) (⤊-ren Γₜ)
            (⊢renameᵀ (ext-h h) (Mono-extᵗ mono) ⊢N))
⊢renameᵀ {ρ} h mono (⊢·[] {L = L} {B = B} {A = A} ⊢L wfA) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ] ⦂ T)
        (sym (rename-[]ᵗ-commute ρ B A))
    (⊢·[] (⊢renameᵀ h mono ⊢L) (wf-ren h wfA))
⊢renameᵀ {ρ} h mono (env {Θ = Θ} {B₀ = B₀} {M = M} bwf sc ⊢M) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ (intRen ρ Θ) M
                       ⟪ renᴮ ρ (intRen ρ Θ) Θ
                       , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫ ⦂ T)
        (C-ext ρ (intRen ρ Θ) Θ B₀)
    (env (bwf-ren h (h-int h mono Θ) bwf) (sc-ren h mono Θ sc)
         (subst (λ T → _ ∣ [] ⊢ renameᵀ (intRen ρ Θ) M ⦂ T)
                (sym (C-int mono Θ sc))
                (⊢renameᵀ (h-int h mono Θ) (Mono-intRen Θ mono) ⊢M)))

------------------------------------------------------------------------
-- Boundary shift (R1).  The face laws of  rvl A ∷ shiftReps Θ  — the
-- boundary TyWrap builds.  The interior face becomes extsᵗ of the old one AT
-- EVERY SLOT (blocked ones included), so R1 carries no scope side-condition
-- of its own; the exterior face instantiates the ∀ with the type argument A.
-- Under the direct-combine TyWrap these laws are the WHOLE preservation case:
-- the Λ-body is already typed at abst ∷ intOf Δ Θ with the extsᵗ face, so it
-- transports by these equations alone — no renaming of the term.
------------------------------------------------------------------------

isConc-shift : ∀ i Θ → isConc i (shiftReps Θ) ≡ isConc i Θ
isConc-shift i []             = refl
isConc-shift i (rvl A   ∷ Θ) = isConc-shift i Θ
isConc-shift i (cnc X A ∷ Θ) = cong (⌊ i ≟ X ⌋ ∨_) (isConc-shift i Θ)

-- shiftReps does not move the reveals, so the EXTERIOR face is untouched
ρᵇ-shift : ∀ Θ X → ρᵇ (shiftReps Θ) X ≡ ρᵇ Θ X
ρᵇ-shift []                   X = refl
ρᵇ-shift (rvl A   ∷ Θ) zero    = refl
ρᵇ-shift (rvl A   ∷ Θ) (suc X) = ρᵇ-shift Θ X
ρᵇ-shift (cnc X A ∷ Θ) Y       = ρᵇ-shift Θ Y

γcnc-shift : ∀ r m Θ i
  → γcnc (suc r) m (shiftReps Θ) i ≡ renameᵗ suc (γcnc r m Θ i)
γcnc-shift r m []             i = refl
γcnc-shift r m (rvl A   ∷ Θ) i = γcnc-shift r m Θ i
γcnc-shift r m (cnc X A ∷ Θ) i with X ≟ i
γcnc-shift r m (cnc X A ∷ Θ) i | yes _ = refl
γcnc-shift r m (cnc X A ∷ Θ) i | no  _ = γcnc-shift r m Θ i

γᵇ-shift-raw : ∀ r c Θ X
  → prepId (suc r) (γcnc (suc r) c (shiftReps Θ)) X
    ≡ extsᵗ (prepId r (γcnc r c Θ)) X
γᵇ-shift-raw r c Θ zero =
  prepId-lo (suc r) (γcnc (suc r) c (shiftReps Θ)) zero (s≤s z≤n)
γᵇ-shift-raw r c Θ (suc j) with split r j
γᵇ-shift-raw r c Θ (suc j) | inj₁ j<r =
  trans (prepId-lo (suc r) (γcnc (suc r) c (shiftReps Θ)) (suc j) (s≤s j<r))
        (cong (renameᵗ suc) (sym (prepId-lo r (γcnc r c Θ) j j<r)))
γᵇ-shift-raw r c Θ (suc j) | inj₂ (i , refl) =
  trans (prepId-hi (suc r) (γcnc (suc r) c (shiftReps Θ)) i)
        (trans (γcnc-shift r c Θ i)
               (cong (renameᵗ suc) (sym (prepId-hi r (γcnc r c Θ) i))))

-- FACE LAW (interior).  Adding the reveal of the type argument and shifting
-- the conceal reps is exactly extsᵗ on the interior face — at EVERY slot.
γᵇ-shift : ∀ A Θ X → γᵇ (rvl A ∷ shiftReps Θ) X ≡ extsᵗ (γᵇ Θ) X
γᵇ-shift A Θ X rewrite revs-shiftReps Θ | cmax-shiftReps Θ =
  γᵇ-shift-raw (revs Θ) (cmax Θ) Θ X

γᵇ-shift-ty : ∀ A Θ B → substᵗ (γᵇ (rvl A ∷ shiftReps Θ)) B
                        ≡ substᵗ (extsᵗ (γᵇ Θ)) B
γᵇ-shift-ty A Θ B = subst-cong (γᵇ-shift A Θ) B

-- FACE LAW (exterior).  The new reveal instantiates the ∀ with A.
ρᵇ-shift-ty : ∀ A Θ B → substᵗ (ρᵇ (rvl A ∷ shiftReps Θ)) B
                        ≡ (substᵗ (extsᵗ (ρᵇ Θ)) B) [ A ]ᵗ
ρᵇ-shift-ty A Θ B =
  trans (subst-cong h B) (sym (exts-sub-cons {σ = ρᵇ Θ} {a = B} {v = A}))
  where
    h : ∀ X → ρᵇ (rvl A ∷ shiftReps Θ) X ≡ cons-sub A (ρᵇ Θ) X
    h zero    = refl
    h (suc X) = ρᵇ-shift Θ X

-- the boundary stays well formed once the interior gains an abstract var
bwf-shiftReps : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ Θ → Δ ∣ (abst ∷ Ψ) ⊢ᵇ shiftReps Θ
bwf-shiftReps []             bwf[]            = bwf[]
bwf-shiftReps (rvl A   ∷ Θ) (bwf↑ wfA bwf)   = bwf↑ wfA (bwf-shiftReps Θ bwf)
bwf-shiftReps (cnc X A ∷ Θ) (bwf↓ p wfA bwf) =
  bwf↓ p (wf-⇑-abst wfA) (bwf-shiftReps Θ bwf)

-- … at the interior the (env) rule actually uses  (intOf-shift)
bwf-shift : ∀ {Δ A} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → Δ ⊢ A
  → Δ ∣ intOf Δ (rvl A ∷ shiftReps Θ) ⊢ᵇ (rvl A ∷ shiftReps Θ)
bwf-shift {Δ} {A} Θ bwf wfA =
  subst (λ Ψ → Δ ∣ Ψ ⊢ᵇ (rvl A ∷ shiftReps Θ))
        (sym (intOf-shift Δ A Θ))
        (bwf↑ wfA (bwf-shiftReps Θ bwf))

-- the scope stack just gains one accessible slot for the new reveal, so R1's
-- Scoped obligation IS the sc-∀ inversion of the redex's
slotAt-shift : ∀ A Θ i → slotAt (rvl A ∷ shiftReps Θ) i ≡ slotAt Θ i
slotAt-shift A Θ i with cmax (shiftReps Θ) ≤? i | cmax Θ ≤? i
slotAt-shift A Θ i | yes _ | yes _ = refl
slotAt-shift A Θ i | yes p | no ¬q =
  ⊥-elim (¬q (subst (_≤ i) (cmax-shiftReps Θ) p))
slotAt-shift A Θ i | no ¬p | yes q =
  ⊥-elim (¬p (subst (_≤ i) (sym (cmax-shiftReps Θ)) q))
slotAt-shift A Θ i | no _  | no _ rewrite isConc-shift i Θ = refl

slotsᴳ-shift : ∀ A Θ k (Γ : TCtx)
  → slotsᴳ (rvl A ∷ shiftReps Θ) k Γ ≡ slotsᴳ Θ k Γ
slotsᴳ-shift A Θ k []      = refl
slotsᴳ-shift A Θ k (E ∷ Γ) =
  cong₂ _∷_ (slotAt-shift A Θ k) (slotsᴳ-shift A Θ (suc k) Γ)

baseS-shift : ∀ A Θ (Γ : TCtx)
  → baseS (rvl A ∷ shiftReps Θ) Γ ≡ ok ∷ baseS Θ Γ
baseS-shift A Θ Γ rewrite revs-shiftReps Θ =
  cong (ok ∷_) (cong (repl-ok (revs Θ) ++_) (slotsᴳ-shift A Θ 0 Γ))

------------------------------------------------------------------------
-- Dual boundary (R2), part 1: the SHAPE of dualᵇ.  Its reveal block is the
-- Δ-prefix Θ drops (so revs Θᵈ = cmax Θ) and its conceal block is Θ's own
-- reveals (so cmax Θᵈ = revs Θ) — the two blocks of the frame swap.
------------------------------------------------------------------------

revs-++ : ∀ Θ₁ Θ₂ → revs (Θ₁ ++ Θ₂) ≡ revs Θ₁ + revs Θ₂
revs-++ []             Θ₂ = refl
revs-++ (rvl A   ∷ Θ₁) Θ₂ = cong suc (revs-++ Θ₁ Θ₂)
revs-++ (cnc X A ∷ Θ₁) Θ₂ = revs-++ Θ₁ Θ₂

cmax-++ : ∀ Θ₁ Θ₂ → cmax (Θ₁ ++ Θ₂) ≡ cmax Θ₁ ⊔ cmax Θ₂
cmax-++ []             Θ₂ = refl
cmax-++ (rvl A   ∷ Θ₁) Θ₂ = cmax-++ Θ₁ Θ₂
cmax-++ (cnc X A ∷ Θ₁) Θ₂ =
  trans (cong (suc X ⊔_) (cmax-++ Θ₁ Θ₂))
        (sym (⊔-assoc (suc X) (cmax Θ₁) (cmax Θ₂)))

revs-rvlsOf : ∀ k s Θ → revs (rvlsOf k s Θ) ≡ k
revs-rvlsOf zero    s Θ = refl
revs-rvlsOf (suc k) s Θ = cong suc (revs-rvlsOf k (suc s) Θ)

cmax-rvlsOf : ∀ k s Θ → cmax (rvlsOf k s Θ) ≡ 0
cmax-rvlsOf zero    s Θ = refl
cmax-rvlsOf (suc k) s Θ = cmax-rvlsOf k (suc s) Θ

revs-cncOfRevs : ∀ j Θ → revs (cncOfRevs j Θ) ≡ 0
revs-cncOfRevs j []             = refl
revs-cncOfRevs j (rvl A   ∷ Θ) = revs-cncOfRevs (suc j) Θ
revs-cncOfRevs j (cnc X A ∷ Θ) = revs-cncOfRevs j Θ

-- the conceals sit at j … j + revs Θ ∸ 1, so the deepest is j + revs Θ
-- (and there is none at all when Θ has no reveal) — stated ⊔ j to cover
-- both shapes at once
cmax-cncOfRevs : ∀ j Θ → cmax (cncOfRevs j Θ) ⊔ j ≡ j + revs Θ
cmax-cncOfRevs j []             = sym (+-identityʳ j)
cmax-cncOfRevs j (rvl A   ∷ Θ) =
  trans (m≥n⇒m⊔n≡m (≤-trans (n≤1+n j)
                            (m≤m⊔n (suc j) (cmax (cncOfRevs (suc j) Θ)))))
    (trans (⊔-comm (suc j) (cmax (cncOfRevs (suc j) Θ)))
      (trans (cmax-cncOfRevs (suc j) Θ) (sym (+-suc j (revs Θ)))))
cmax-cncOfRevs j (cnc X A ∷ Θ) = cmax-cncOfRevs j Θ

cmax-cncOfRevs0 : ∀ Θ → cmax (cncOfRevs 0 Θ) ≡ revs Θ
cmax-cncOfRevs0 Θ =
  trans (sym (⊔-identityʳ (cmax (cncOfRevs 0 Θ)))) (cmax-cncOfRevs 0 Θ)

revs-dual : ∀ Θ → revs (dualᵇ Θ) ≡ cmax Θ
revs-dual Θ =
  trans (revs-++ (rvlsOf (cmax Θ) 0 Θ) (cncOfRevs 0 Θ))
    (trans (cong₂ _+_ (revs-rvlsOf (cmax Θ) 0 Θ) (revs-cncOfRevs 0 Θ))
           (+-identityʳ (cmax Θ)))

cmax-dual : ∀ Θ → cmax (dualᵇ Θ) ≡ revs Θ
cmax-dual Θ =
  trans (cmax-++ (rvlsOf (cmax Θ) 0 Θ) (cncOfRevs 0 Θ))
    (trans (cong (_⊔ cmax (cncOfRevs 0 Θ)) (cmax-rvlsOf (cmax Θ) 0 Θ))
           (cmax-cncOfRevs0 Θ))

------------------------------------------------------------------------
-- Part 2: the CONTEXT law and the retagging it needs.
--
-- intOf (intOf Δ Θ) (dualᵇ Θ) = prepAbst c (dropN c Δ) — the dual's
-- interior REBUILDS the exterior, but with the dropped prefix rebuilt as
-- `abst.  Over an all-`abst` Δ that is Δ on the nose; over a Δ with `rvld`
-- entries in the dropped prefix it is NOT (no boundary has interior Γ₃ —
-- notes/BoundaryRulesProbe §3b).  It does not have to be: typing reads a
-- TCtx only through _∋tv_ and _⊢_, neither of which inspects the marker,
-- so a derivation transports along ANY context of the same length
-- (⊢retag).  That is what keeps preservation's statement unchanged.
------------------------------------------------------------------------

dropN-prepAbst : ∀ r (Γ : TCtx) → dropN r (prepAbst r Γ) ≡ Γ
dropN-prepAbst zero    Γ = refl
dropN-prepAbst (suc r) Γ = dropN-prepAbst r Γ

intOf-dual : ∀ (Δ : TCtx) Θ
  → intOf (intOf Δ Θ) (dualᵇ Θ) ≡ prepAbst (cmax Θ) (dropN (cmax Θ) Δ)
intOf-dual Δ Θ rewrite revs-dual Θ | cmax-dual Θ =
  cong (prepAbst (cmax Θ)) (dropN-prepAbst (revs Θ) (dropN (cmax Θ) Δ))

len-dropN : ∀ c (Γ : TCtx) → length (dropN c Γ) ≡ length Γ ∸ c
len-dropN zero    Γ       = refl
len-dropN (suc c) []      = refl
len-dropN (suc c) (E ∷ Γ) = len-dropN c Γ

len-prepAbst : ∀ r (Γ : TCtx) → length (prepAbst r Γ) ≡ r + length Γ
len-prepAbst zero    Γ = refl
len-prepAbst (suc r) Γ = cong suc (len-prepAbst r Γ)

len-intOf : ∀ (Γ : TCtx) Θ
          → length (intOf Γ Θ) ≡ revs Θ + (length Γ ∸ cmax Θ)
len-intOf Γ Θ = trans (len-prepAbst (revs Θ) (dropN (cmax Θ) Γ))
                      (cong (revs Θ +_) (len-dropN (cmax Θ) Γ))

len-dual : ∀ (Δ : TCtx) Θ → cmax Θ ≤ length Δ
         → length Δ ≡ length (intOf (intOf Δ Θ) (dualᵇ Θ))
len-dual Δ Θ le =
  sym (trans (cong length (intOf-dual Δ Θ))
        (trans (len-prepAbst (cmax Θ) (dropN (cmax Θ) Δ))
          (trans (cong (cmax Θ +_) (len-dropN (cmax Θ) Δ))
                 (m+[n∸m]≡n le))))

-- the deepest conceal is a variable of Δ, so the dropped prefix is no
-- longer than Δ — the side condition len-dual needs
∋tv-len-bound : ∀ {Γ : TCtx} {X} → Γ ∋tv X → suc X ≤ length Γ
∋tv-len-bound here-abst     = s≤s z≤n
∋tv-len-bound here-rvld     = s≤s z≤n
∋tv-len-bound (skip-abst p) = s≤s (∋tv-len-bound p)
∋tv-len-bound (skip-rvld p) = s≤s (∋tv-len-bound p)

bwf-cmax : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ Θ → cmax Θ ≤ length Δ
bwf-cmax []             bwf[]          = z≤n
bwf-cmax (rvl A   ∷ Θ) (bwf↑ wfA b)   = bwf-cmax Θ b
bwf-cmax (cnc X A ∷ Θ) (bwf↓ p wfA b) =
  ⊔-lub (∋tv-len-bound p) (bwf-cmax Θ b)

∋tv-len : ∀ {Γ Γ' : TCtx} {X} → length Γ ≡ length Γ' → Γ ∋tv X → Γ' ∋tv X
∋tv-len {Γ' = []}          ()  here-abst
∋tv-len {Γ' = abst ∷ Γ'}   le  here-abst     = here-abst
∋tv-len {Γ' = rvld A ∷ Γ'} le  here-abst     = here-rvld
∋tv-len {Γ' = []}          ()  here-rvld
∋tv-len {Γ' = abst ∷ Γ'}   le  here-rvld     = here-abst
∋tv-len {Γ' = rvld A ∷ Γ'} le  here-rvld     = here-rvld
∋tv-len {Γ' = []}          ()  (skip-abst p)
∋tv-len {Γ' = abst ∷ Γ'}   le  (skip-abst p) =
  skip-abst (∋tv-len (suc-injective le) p)
∋tv-len {Γ' = rvld A ∷ Γ'} le  (skip-abst p) =
  skip-rvld (∋tv-len (suc-injective le) p)
∋tv-len {Γ' = []}          ()  (skip-rvld p)
∋tv-len {Γ' = abst ∷ Γ'}   le  (skip-rvld p) =
  skip-abst (∋tv-len (suc-injective le) p)
∋tv-len {Γ' = rvld A ∷ Γ'} le  (skip-rvld p) =
  skip-rvld (∋tv-len (suc-injective le) p)

wf-retag : ∀ {Γ Γ' : TCtx} {A} → length Γ ≡ length Γ' → Γ ⊢ A → Γ' ⊢ A
wf-retag le (wf-var p)  = wf-var (∋tv-len le p)
wf-retag le wf-ℕ        = wf-ℕ
wf-retag le wf-𝔹        = wf-𝔹
wf-retag le (wf-⇒ a b)  = wf-⇒ (wf-retag le a) (wf-retag le b)
wf-retag le (wf-∀ a)    = wf-∀ (wf-retag (cong suc le) a)

bwf-retag : ∀ {Δ Δ' Ψ Ψ' : TCtx} {Θ} → length Δ ≡ length Δ'
  → length Ψ ≡ length Ψ' → Δ ∣ Ψ ⊢ᵇ Θ → Δ' ∣ Ψ' ⊢ᵇ Θ
bwf-retag lΔ lΨ bwf[]           = bwf[]
bwf-retag lΔ lΨ (bwf↑ wfA b)    =
  bwf↑ (wf-retag lΔ wfA) (bwf-retag lΔ lΨ b)
bwf-retag lΔ lΨ (bwf↓ p wfA b)  =
  bwf↓ (∋tv-len lΔ p) (wf-retag lΨ wfA) (bwf-retag lΔ lΨ b)

slotsᴳ-len : ∀ Θ k (Γ Γ' : TCtx) → length Γ ≡ length Γ'
           → slotsᴳ Θ k Γ ≡ slotsᴳ Θ k Γ'
slotsᴳ-len Θ k []      []        le = refl
slotsᴳ-len Θ k []      (E' ∷ Γ') ()
slotsᴳ-len Θ k (E ∷ Γ) []        ()
slotsᴳ-len Θ k (E ∷ Γ) (E' ∷ Γ') le =
  cong (slotAt Θ k ∷_) (slotsᴳ-len Θ (suc k) Γ Γ' (suc-injective le))

baseS-len : ∀ Θ (Γ Γ' : TCtx) → length Γ ≡ length Γ'
          → baseS Θ Γ ≡ baseS Θ Γ'
baseS-len Θ Γ Γ' le =
  cong (repl-ok (revs Θ) ++_) (slotsᴳ-len Θ 0 Γ Γ' le)

-- typing depends on the type context only through its LENGTH: _∋tv_ and
-- _⊢_ ignore the abst/rvld marker, intOf and baseS read only the shape
⊢retag : ∀ {Δ Δ' Γₜ M A} → length Δ ≡ length Δ'
       → Δ ∣ Γₜ ⊢ M ⦂ A → Δ' ∣ Γₜ ⊢ M ⦂ A
⊢retag le (⊢` p)        = ⊢` p
⊢retag le ⊢$            = ⊢$
⊢retag le (⊢ƛ wfA ⊢N)   = ⊢ƛ (wf-retag le wfA) (⊢retag le ⊢N)
⊢retag le (⊢· ⊢L ⊢M)    = ⊢· (⊢retag le ⊢L) (⊢retag le ⊢M)
⊢retag le (⊢Λ ⊢N)       = ⊢Λ (⊢retag (cong suc le) ⊢N)
⊢retag le (⊢·[] ⊢L wfA) = ⊢·[] (⊢retag le ⊢L) (wf-retag le wfA)
⊢retag {Δ} {Δ'} le (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) =
  env (bwf-retag le lint bwf)
      (subst (λ Ψ → Scoped Ψ B₀) (baseS-len Θ Δ Δ' le) sc)
      (⊢retag lint ⊢M)
  where
    lint : length (intOf Δ Θ) ≡ length (intOf Δ' Θ)
    lint = trans (len-intOf Δ Θ)
                 (trans (cong (λ n → revs Θ + (n ∸ cmax Θ)) le)
                        (sym (len-intOf Δ' Θ)))

------------------------------------------------------------------------
-- Part 3: the two FACE laws.  On Θ's boundary frame the slot X is sent by
-- swapᵇ to the slot of Θᵈ's frame holding the same variable, and there
--   ρᵇ Θᵈ ∘ swapᵇ Θ = γᵇ Θ    (at ACCESSIBLE slots only)
--   γᵇ Θᵈ ∘ swapᵇ Θ = ρᵇ Θ    (at every slot)
-- The first fails at a blocked slot — the dual reveals it at the dummy rep
-- while γᵇ aliases it onto a kept variable — which is why R2 goes through
-- subst-cong-sc with (env)'s scope premise (blocked-slot-differs, probe
-- §3a, is the checked witness).
------------------------------------------------------------------------

sover-hit : ∀ X A σ i → X ≡ i → sover X A σ i ≡ A
sover-hit X A σ i e with X ≟ i
sover-hit X A σ i e | yes _  = refl
sover-hit X A σ i e | no ¬e  = ⊥-elim (¬e e)

sover-miss : ∀ X A σ i → ¬ (X ≡ i) → sover X A σ i ≡ σ i
sover-miss X A σ i ne with X ≟ i
sover-miss X A σ i ne | yes e = ⊥-elim (ne e)
sover-miss X A σ i ne | no _  = refl

j≢j+suc : ∀ j k → ¬ (j ≡ j + suc k)
j≢j+suc zero    k ()
j≢j+suc (suc j) k e = j≢j+suc j k (suc-injective e)

isConc-< : ∀ Θ i → isConc i Θ ≡ true → i < cmax Θ
isConc-< []             i ()
isConc-< (rvl A   ∷ Θ) i c = isConc-< Θ i c
isConc-< (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-< (cnc X A ∷ Θ) i c | inj₁ refl = m≤m⊔n (suc i) (cmax Θ)
isConc-< (cnc X A ∷ Θ) i c | inj₂ t =
  ≤-trans (isConc-< Θ i t) (m≤n⊔m (suc X) (cmax Θ))

-- the interior face at a Γ-slot: a concealed one goes to its rep, a kept
-- one to its interior slot
γcnc-conc : ∀ r m Θ i → isConc i Θ ≡ true → γcnc r m Θ i ≡ repOf i Θ
γcnc-conc r m []             i ()
γcnc-conc r m (rvl A   ∷ Θ) i c = γcnc-conc r m Θ i c
γcnc-conc r m (cnc X A ∷ Θ) i c with X ≟ i | i ≟ X
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | yes q = refl
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | no ¬q = ⊥-elim (¬q (sym p))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | yes q = ⊥-elim (¬p (sym q))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | no ¬q =
  γcnc-conc r m Θ i c

γcnc-kept : ∀ r m Θ i → cmax Θ ≤ i → γcnc r m Θ i ≡ ` (r + (i ∸ m))
γcnc-kept r m []             i le = refl
γcnc-kept r m (rvl A   ∷ Θ) i le = γcnc-kept r m Θ i le
γcnc-kept r m (cnc X A ∷ Θ) i le =
  trans (sover-miss X A (γcnc r m Θ) i ne)
        (γcnc-kept r m Θ i (≤-trans (m≤n⊔m (suc X) (cmax Θ)) le))
  where
    ne : ¬ (X ≡ i)
    ne p = <-irrefl p (≤-trans (m≤m⊔n (suc X) (cmax Θ)) le)

γᵇ-conc : ∀ Θ i → isConc i Θ ≡ true → γᵇ Θ (revs Θ + i) ≡ repOf i Θ
γᵇ-conc Θ i c =
  trans (prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i)
        (γcnc-conc (revs Θ) (cmax Θ) Θ i c)

γᵇ-kept : ∀ Θ i → cmax Θ ≤ i
        → γᵇ Θ (revs Θ + i) ≡ ` (revs Θ + (i ∸ cmax Θ))
γᵇ-kept Θ i le =
  trans (prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i)
        (γcnc-kept (revs Θ) (cmax Θ) Θ i le)

-- the exterior face is the identity on the Γ-part of the boundary frame
ρᵇ-hi : ∀ Θ i → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-hi []             i = refl
ρᵇ-hi (rvl A   ∷ Θ) i = ρᵇ-hi Θ i
ρᵇ-hi (cnc X A ∷ Θ) i = ρᵇ-hi Θ i

-- the exterior face of the DUAL: its reveal block resolves the dropped
-- slots to Θ's conceal reps, and everything above it passes through
ρᵇ-rvls-lo : ∀ k s Θ Θ₂ i → i < k
           → ρᵇ (rvlsOf k s Θ ++ Θ₂) i ≡ repOf (s + i) Θ
ρᵇ-rvls-lo zero    s Θ Θ₂ i       ()
ρᵇ-rvls-lo (suc k) s Θ Θ₂ zero    lt =
  cong (λ n → repOf n Θ) (sym (+-identityʳ s))
ρᵇ-rvls-lo (suc k) s Θ Θ₂ (suc i) (s≤s lt) =
  trans (ρᵇ-rvls-lo k (suc s) Θ Θ₂ i lt)
        (cong (λ n → repOf n Θ) (sym (+-suc s i)))

ρᵇ-rvls-hi : ∀ k s Θ Θ₂ j → ρᵇ (rvlsOf k s Θ ++ Θ₂) (k + j) ≡ ρᵇ Θ₂ j
ρᵇ-rvls-hi zero    s Θ Θ₂ j = refl
ρᵇ-rvls-hi (suc k) s Θ Θ₂ j = ρᵇ-rvls-hi k (suc s) Θ Θ₂ j

ρᵇ-cncOfRevs : ∀ j Θ i → ρᵇ (cncOfRevs j Θ) i ≡ ` i
ρᵇ-cncOfRevs j []             i = refl
ρᵇ-cncOfRevs j (rvl A   ∷ Θ) i = ρᵇ-cncOfRevs (suc j) Θ i
ρᵇ-cncOfRevs j (cnc X A ∷ Θ) i = ρᵇ-cncOfRevs j Θ i

ρᵇ-dual-lo : ∀ Θ i → i < cmax Θ → ρᵇ (dualᵇ Θ) i ≡ repOf i Θ
ρᵇ-dual-lo Θ i lt = ρᵇ-rvls-lo (cmax Θ) 0 Θ (cncOfRevs 0 Θ) i lt

ρᵇ-dual-hi : ∀ Θ k → ρᵇ (dualᵇ Θ) (cmax Θ + k) ≡ ` k
ρᵇ-dual-hi Θ k =
  trans (ρᵇ-rvls-hi (cmax Θ) 0 Θ (cncOfRevs 0 Θ) k) (ρᵇ-cncOfRevs 0 Θ k)

-- the interior face of the DUAL: its conceal block resolves Θ's reveal
-- variables to Θ's own reveal reps, and everything above it is kept
γcnc-rvls : ∀ r m k s Θ Θ₂ i
  → γcnc r m (rvlsOf k s Θ ++ Θ₂) i ≡ γcnc r m Θ₂ i
γcnc-rvls r m zero    s Θ Θ₂ i = refl
γcnc-rvls r m (suc k) s Θ Θ₂ i = γcnc-rvls r m k (suc s) Θ Θ₂ i

γcnc-cnc-lo : ∀ r m j Θ k → k < revs Θ
  → γcnc r m (cncOfRevs j Θ) (j + k) ≡ ρᵇ Θ k
γcnc-cnc-lo r m j []             k       ()
γcnc-cnc-lo r m j (rvl A   ∷ Θ) zero    lt =
  sover-hit j A (γcnc r m (cncOfRevs (suc j) Θ)) (j + 0)
            (sym (+-identityʳ j))
γcnc-cnc-lo r m j (rvl A   ∷ Θ) (suc k) (s≤s lt) =
  trans (sover-miss j A (γcnc r m (cncOfRevs (suc j) Θ)) (j + suc k)
                    (j≢j+suc j k))
    (trans (cong (γcnc r m (cncOfRevs (suc j) Θ)) (+-suc j k))
           (γcnc-cnc-lo r m (suc j) Θ k lt))
γcnc-cnc-lo r m j (cnc X A ∷ Θ) k       lt = γcnc-cnc-lo r m j Θ k lt

γcnc-cnc-hi : ∀ r m j Θ i → j + revs Θ ≤ i
  → γcnc r m (cncOfRevs j Θ) i ≡ ` (r + (i ∸ m))
γcnc-cnc-hi r m j []             i le = refl
γcnc-cnc-hi r m j (rvl A   ∷ Θ) i le =
  trans (sover-miss j A (γcnc r m (cncOfRevs (suc j) Θ)) i ne)
        (γcnc-cnc-hi r m (suc j) Θ i le')
  where
    le' : suc j + revs Θ ≤ i
    le' = subst (_≤ i) (+-suc j (revs Θ)) le
    ne : ¬ (j ≡ i)
    ne p = <-irrefl p (≤-trans (s≤s (m≤m+n j (revs Θ))) le')
γcnc-cnc-hi r m j (cnc X A ∷ Θ) i le = γcnc-cnc-hi r m j Θ i le

γᵇ-dual-lo : ∀ Θ i → i < cmax Θ → γᵇ (dualᵇ Θ) i ≡ ` i
γᵇ-dual-lo Θ i lt =
  prepId-lo (revs (dualᵇ Θ))
            (γcnc (revs (dualᵇ Θ)) (cmax (dualᵇ Θ)) (dualᵇ Θ)) i
            (subst (i <_) (sym (revs-dual Θ)) lt)

γᵇ-dual-hi : ∀ Θ k
  → γᵇ (dualᵇ Θ) (cmax Θ + k) ≡ γcnc (cmax Θ) (revs Θ) (dualᵇ Θ) k
γᵇ-dual-hi Θ k =
  trans (prepId-hi′ (cmax Θ) (revs (dualᵇ Θ))
                    (γcnc (revs (dualᵇ Θ)) (cmax (dualᵇ Θ)) (dualᵇ Θ)) k
                    (revs-dual Θ))
        (cong₂ (λ a b → γcnc a b (dualᵇ Θ) k) (revs-dual Θ) (cmax-dual Θ))

γcnc-dual-lo : ∀ Θ k → k < revs Θ
  → γcnc (cmax Θ) (revs Θ) (dualᵇ Θ) k ≡ ρᵇ Θ k
γcnc-dual-lo Θ k lt =
  trans (γcnc-rvls (cmax Θ) (revs Θ) (cmax Θ) 0 Θ (cncOfRevs 0 Θ) k)
        (γcnc-cnc-lo (cmax Θ) (revs Θ) 0 Θ k lt)

γcnc-dual-hi : ∀ Θ k → revs Θ ≤ k
  → γcnc (cmax Θ) (revs Θ) (dualᵇ Θ) k ≡ ` (cmax Θ + (k ∸ revs Θ))
γcnc-dual-hi Θ k le =
  trans (γcnc-rvls (cmax Θ) (revs Θ) (cmax Θ) 0 Θ (cncOfRevs 0 Θ) k)
        (γcnc-cnc-hi (cmax Θ) (revs Θ) 0 Θ k le)

-- the frame permutation, on the three regions of Θ's frame
swap-lo : ∀ r c X → X < r → swapIdx r c X ≡ c + X
swap-lo r c X lt with X <? r
swap-lo r c X lt | yes _  = refl
swap-lo r c X lt | no ¬lt = ⊥-elim (¬lt lt)

swap-mid : ∀ r c i → i < c → swapIdx r c (r + i) ≡ i
swap-mid r c i lt with (r + i) <? r
swap-mid r c i lt | yes p = ⊥-elim (m+n≮m r i p)
swap-mid r c i lt | no ¬p with ((r + i) ∸ r) <? c
swap-mid r c i lt | no ¬p | yes q = m+n∸m≡n r i
swap-mid r c i lt | no ¬p | no ¬q =
  ⊥-elim (¬q (subst (_< c) (sym (m+n∸m≡n r i)) lt))

swap-hi : ∀ r c i → c ≤ i → swapIdx r c (r + i) ≡ r + i
swap-hi r c i le with (r + i) <? r
swap-hi r c i le | yes p = ⊥-elim (m+n≮m r i p)
swap-hi r c i le | no ¬p with ((r + i) ∸ r) <? c
swap-hi r c i le | no ¬p | yes q =
  ⊥-elim (<-irrefl refl (≤-trans (subst (_< c) (m+n∸m≡n r i) q) le))
swap-hi r c i le | no ¬p | no ¬q = refl

-- a kept slot keeps its position: c + (r + (i ∸ c)) = r + i
kept-idx : ∀ r c i → c ≤ i → c + (r + (i ∸ c)) ≡ r + i
kept-idx r c i le =
  trans (sym (+-assoc c r (i ∸ c)))
    (trans (cong (_+ (i ∸ c)) (+-comm c r))
      (trans (+-assoc r c (i ∸ c)) (cong (r +_) (m+[n∸m]≡n le))))

-- FACE LAW (exterior of the dual = interior of Θ), at accessible slots
ρᵇ-dual-swap : ∀ {Δ} Θ X → baseS Θ Δ ∋ok X
             → ρᵇ (dualᵇ Θ) (swapᵇ Θ X) ≡ γᵇ Θ X
ρᵇ-dual-swap Θ X okp with split (revs Θ) X
ρᵇ-dual-swap Θ X okp | inj₁ lt =
  trans (cong (ρᵇ (dualᵇ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
    (trans (ρᵇ-dual-hi Θ X)
           (sym (prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X lt)))
ρᵇ-dual-swap Θ .(revs Θ + i) okp | inj₂ (i , refl)
  with baseS-acc Θ i okp
ρᵇ-dual-swap Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  trans (cong (ρᵇ (dualᵇ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (ρᵇ-dual-hi Θ (revs Θ + (i ∸ cmax Θ))) (sym (γᵇ-kept Θ i le)))
ρᵇ-dual-swap Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  trans (cong (ρᵇ (dualᵇ Θ))
              (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
    (trans (ρᵇ-dual-lo Θ i (isConc-< Θ i cc)) (sym (γᵇ-conc Θ i cc)))

-- FACE LAW (interior of the dual = exterior of Θ), at EVERY slot
γᵇ-dual-swap : ∀ Θ X → γᵇ (dualᵇ Θ) (swapᵇ Θ X) ≡ ρᵇ Θ X
γᵇ-dual-swap Θ X with split (revs Θ) X
γᵇ-dual-swap Θ X | inj₁ lt =
  trans (cong (γᵇ (dualᵇ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
        (trans (γᵇ-dual-hi Θ X) (γcnc-dual-lo Θ X lt))
γᵇ-dual-swap Θ .(revs Θ + i) | inj₂ (i , refl) with cmax Θ ≤? i
γᵇ-dual-swap Θ .(revs Θ + i) | inj₂ (i , refl) | yes le =
  trans (cong (γᵇ (dualᵇ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (γᵇ-dual-hi Θ (revs Θ + (i ∸ cmax Θ)))
      (trans (γcnc-dual-hi Θ (revs Θ + (i ∸ cmax Θ))
                           (m≤m+n (revs Θ) (i ∸ cmax Θ)))
        (trans (cong (λ n → ` (cmax Θ + n))
                     (m+n∸m≡n (revs Θ) (i ∸ cmax Θ)))
          (trans (cong `_ (m+[n∸m]≡n le)) (sym (ρᵇ-hi Θ i))))))
γᵇ-dual-swap Θ .(revs Θ + i) | inj₂ (i , refl) | no ¬le =
  trans (cong (γᵇ (dualᵇ Θ)) (swap-mid (revs Θ) (cmax Θ) i (≰⇒> ¬le)))
        (trans (γᵇ-dual-lo Θ i (≰⇒> ¬le)) (sym (ρᵇ-hi Θ i)))

-- the two face laws as the retypings preservation needs.  The exterior one
-- is scope-restricted (subst-cong-sc with (env)'s premise for B₁).
ρᵇ-dual-ty : ∀ {Δ} B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (ρᵇ (dualᵇ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (γᵇ Θ) B
ρᵇ-dual-ty B Θ sc =
  trans (rename-subst-commute (swapᵇ Θ) (ρᵇ (dualᵇ Θ)) B)
        (subst-cong-sc sc (λ X okp → ρᵇ-dual-swap Θ X okp))

γᵇ-dual-ty : ∀ B Θ
  → substᵗ (γᵇ (dualᵇ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (ρᵇ Θ) B
γᵇ-dual-ty B Θ =
  trans (rename-subst-commute (swapᵇ Θ) (γᵇ (dualᵇ Θ)) B)
        (subst-cong (γᵇ-dual-swap Θ) B)

------------------------------------------------------------------------
-- Part 4: the dual is WELL FORMED and its scope stack is all-accessible.
-- Reveal reps of Θᵈ are Θ's conceal reps, which bwf reads in intOf Δ Θ =
-- Θᵈ's exterior; conceal reps of Θᵈ are Θ's reveal reps, which bwf reads
-- in Δ = Θᵈ's interior (up to retagging).  Every slot of Θᵈ's frame is
-- accessible: below cmax Θᵈ = revs Θ every index is concealed by Θᵈ.
------------------------------------------------------------------------

bwf-++ : ∀ {Γ Ψ} Θ₁ Θ₂ → Γ ∣ Ψ ⊢ᵇ Θ₁ → Γ ∣ Ψ ⊢ᵇ Θ₂ → Γ ∣ Ψ ⊢ᵇ (Θ₁ ++ Θ₂)
bwf-++ []             Θ₂ bwf[]          b₂ = b₂
bwf-++ (rvl A   ∷ Θ₁) Θ₂ (bwf↑ wfA b)   b₂ = bwf↑ wfA (bwf-++ Θ₁ Θ₂ b b₂)
bwf-++ (cnc X A ∷ Θ₁) Θ₂ (bwf↓ p wfA b) b₂ =
  bwf↓ p wfA (bwf-++ Θ₁ Θ₂ b b₂)

repOf-wf : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ Θ → ∀ i → Ψ ⊢ repOf i Θ
repOf-wf []             bwf[]          i = wf-ℕ
repOf-wf (rvl A   ∷ Θ) (bwf↑ wfA b)   i = repOf-wf Θ b i
repOf-wf (cnc X A ∷ Θ) (bwf↓ p wfA b) i with i ≟ X
repOf-wf (cnc X A ∷ Θ) (bwf↓ p wfA b) i | yes q = wfA
repOf-wf (cnc X A ∷ Θ) (bwf↓ p wfA b) i | no ¬q = repOf-wf Θ b i

bwf-rvlsOf : ∀ {Δ Ψ Δ'} Θ → Δ ∣ Ψ ⊢ᵇ Θ → ∀ k s → Ψ ∣ Δ' ⊢ᵇ rvlsOf k s Θ
bwf-rvlsOf Θ b zero    s = bwf[]
bwf-rvlsOf Θ b (suc k) s =
  bwf↑ (repOf-wf Θ b s) (bwf-rvlsOf Θ b k (suc s))

bwf-cncOfRevs : ∀ {Δ Ψ Δ'} Θ → Δ ∣ Ψ ⊢ᵇ Θ → length Δ ≡ length Δ'
  → ∀ j → (∀ k → k < revs Θ → Ψ ∋tv (j + k))
  → Ψ ∣ Δ' ⊢ᵇ cncOfRevs j Θ
bwf-cncOfRevs {Δ} {Ψ} []             bwf[]          le j h = bwf[]
bwf-cncOfRevs {Δ} {Ψ} (rvl A   ∷ Θ) (bwf↑ wfA b)   le j h =
  bwf↓ (subst (Ψ ∋tv_) (+-identityʳ j) (h 0 (s≤s z≤n)))
       (wf-retag le wfA)
       (bwf-cncOfRevs Θ b le (suc j) h′)
  where
    h′ : ∀ k → k < revs Θ → Ψ ∋tv (suc j + k)
    h′ k lt = subst (Ψ ∋tv_) (+-suc j k) (h (suc k) (s≤s lt))
bwf-cncOfRevs {Δ} {Ψ} (cnc X A ∷ Θ) (bwf↓ p wfA b) le j h =
  bwf-cncOfRevs Θ b le j h

bwf-dual : ∀ {Δ Δ'} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → length Δ ≡ length Δ'
         → intOf Δ Θ ∣ Δ' ⊢ᵇ dualᵇ Θ
bwf-dual {Δ} Θ bwf le =
  bwf-++ (rvlsOf (cmax Θ) 0 Θ) (cncOfRevs 0 Θ)
         (bwf-rvlsOf Θ bwf (cmax Θ) 0)
         (bwf-cncOfRevs Θ bwf le 0 h)
  where
    h : ∀ k → k < revs Θ → intOf Δ Θ ∋tv (0 + k)
    h k lt = prepAbst-lo (revs Θ) (dropN (cmax Θ) Δ) k lt

isConc-++ʳ : ∀ i Θ₁ Θ₂ → isConc i Θ₂ ≡ true → isConc i (Θ₁ ++ Θ₂) ≡ true
isConc-++ʳ i []             Θ₂ c = c
isConc-++ʳ i (rvl A   ∷ Θ₁) Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c
isConc-++ʳ i (cnc X A ∷ Θ₁) Θ₂ c =
  isConc-there i X A (Θ₁ ++ Θ₂) (isConc-++ʳ i Θ₁ Θ₂ c)

isConc-cncOfRevs : ∀ j Θ k → k < revs Θ
                 → isConc (j + k) (cncOfRevs j Θ) ≡ true
isConc-cncOfRevs j []             k       ()
isConc-cncOfRevs j (rvl A   ∷ Θ) zero    lt =
  isConc-here (j + 0) j A (cncOfRevs (suc j) Θ) (+-identityʳ j)
isConc-cncOfRevs j (rvl A   ∷ Θ) (suc k) (s≤s lt) =
  isConc-there (j + suc k) j A (cncOfRevs (suc j) Θ)
    (subst (λ n → isConc n (cncOfRevs (suc j) Θ) ≡ true)
           (sym (+-suc j k)) (isConc-cncOfRevs (suc j) Θ k lt))
isConc-cncOfRevs j (cnc X A ∷ Θ) k       lt = isConc-cncOfRevs j Θ k lt

isConc-dual : ∀ Θ k → k < revs Θ → isConc k (dualᵇ Θ) ≡ true
isConc-dual Θ k lt =
  isConc-++ʳ k (rvlsOf (cmax Θ) 0 Θ) (cncOfRevs 0 Θ)
             (isConc-cncOfRevs 0 Θ k lt)

dropN-∋tv : ∀ c (Γ : TCtx) i → c ≤ i → Γ ∋tv i → dropN c Γ ∋tv (i ∸ c)
dropN-∋tv zero    Γ       i       le       p = p
dropN-∋tv (suc c) []      i       le       ()
dropN-∋tv (suc c) (E ∷ Γ) zero    ()       p
dropN-∋tv (suc c) (E ∷ Γ) (suc i) (s≤s le) p =
  dropN-∋tv c Γ i le (∋tv-tail p)

-- every slot of the dual's frame is ACCESSIBLE, and swapᵇ lands on the
-- slot holding the same variable
swap-ok : ∀ {Δ} Θ X → baseS Θ Δ ∋ok X
        → baseS (dualᵇ Θ) (intOf Δ Θ) ∋ok swapᵇ Θ X
swap-ok {Δ} Θ X okp with split (revs Θ) X
swap-ok {Δ} Θ X okp | inj₁ lt =
  ∋ok-≡ (trans (cong (_+ X) (revs-dual Θ))
               (sym (swap-lo (revs Θ) (cmax Θ) X lt)))
        (baseS-ok (dualᵇ Θ) X (inj₂ (isConc-dual Θ X lt))
                  (prepAbst-lo (revs Θ) (dropN (cmax Θ) Δ) X lt))
swap-ok {Δ} Θ .(revs Θ + i) okp | inj₂ (i , refl) with baseS-acc Θ i okp
swap-ok {Δ} Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  ∋ok-≡ (trans (cong (_+ (revs Θ + (i ∸ cmax Θ))) (revs-dual Θ))
          (trans (kept-idx (revs Θ) (cmax Θ) i le)
                 (sym (swap-hi (revs Θ) (cmax Θ) i le))))
        (baseS-ok (dualᵇ Θ) (revs Θ + (i ∸ cmax Θ))
                  (inj₁ (subst (_≤ revs Θ + (i ∸ cmax Θ)) (sym (cmax-dual Θ))
                               (m≤m+n (revs Θ) (i ∸ cmax Θ))))
                  (prepAbst-hi (revs Θ) (dropN (cmax Θ) Δ) (i ∸ cmax Θ)
                    (dropN-∋tv (cmax Θ) Δ i le (baseS-∋tv Θ i okp))))
swap-ok {Δ} Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  ∋ok-≡ (sym (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
        (repl-lo (revs (dualᵇ Θ)) i
                 (subst (i <_) (sym (revs-dual Θ)) (isConc-< Θ i cc)))

sc-dual : ∀ {Δ B} Θ → Scoped (baseS Θ Δ) B
        → Scoped (baseS (dualᵇ Θ) (intOf Δ Θ)) (renameᵗ (swapᵇ Θ) B)
sc-dual Θ sc = sc-rename (λ X okp → swap-ok Θ X okp) sc
