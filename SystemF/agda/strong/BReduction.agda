module strong.BReduction where

-- Reduction for the tight dual boundary (B₀) design, one rule at a time.
-- Each rule: the rule, a worked typed example, and its preservation case.
-- Preservation is stated at runtime term contexts ([]).
--
-- Reduction is KNOWLEDGE-INDEXED (notes/DECISIONS.md, Decision 4's ambient
-- dual): the judgement is  Δ ⊢ M -→ M′, mirroring the Δ of typing.  ξ-⟪⟫
-- extends the index by the boundary's interior and ξ-Λ by an abstract entry;
-- every other rule passes Δ through.  Only Wrap reads it — its dual copies
-- the ambient context's own entry at each slot the boundary drops without
-- concealing, so no knowledge is ever lost and no term traversal is needed.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _⊔_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; +-monoʳ-<; +-cancelˡ-<; ≤-trans; <⇒≤; ≤-refl;
         _≟_; <-cmp; <-irrefl; ≰⇒>; m≤n⇒m<n∨m≡n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m;
         m+n∸m≡n; m+n≮m; +-identityʳ; +-suc; +-assoc; +-comm;
         ⊔-assoc; ⊔-comm; ⊔-identityʳ; ⊔-lub; m≤m⊔n;
         n≤1+n; suc-injective; m≤n⊔m; ≤⇒≯; +-cancelˡ-≡; ≤-pred;
         +-cancelˡ-≤; +-monoʳ-≤; +-∸-assoc; ∸-+-assoc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Nullary using (Dec; yes; no; ¬_; ⌊_⌋)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂; cong; cong₂)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-cong; rename-rename-commute; rename-[]ᵗ-commute;
         rename-subst; rename-subst-commute; exts-sub-cons; cons-sub;
         subst-id)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld;
         skip-abst; skip-rvld; _∋_:=_; here; ∋:=→∋tv;
         Ctx; _∋_⦂_; there; ⤊)
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

-- Renaming a wrapper's type variables (ρ : Γ → Γ').  A REVEAL rep is now a
-- type over the frame of its own TAIL (the telescopic reveal block), so it
-- renames by liftⁿ (revs Ξ) ρ; conceal indices rename by ρ; B₀ lives over the
-- boundary frame (reveals ++ Γ) so it renames by liftⁿ (revs Θ) ρ; the body
-- and conceal reps live over the interior, which renames by intRen —
-- identity below a conceal that absorbs ρ (a conceal restricts to Γ↓X, and
-- restrictRen X ρ is the induced renaming on Γ↓X).
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

renᴮ : (ℕ → ℕ) → (ℕ → ℕ) → BCtx → BCtx
renᴮ ρ ir []            = []
renᴮ ρ ir (rvl A ∷ Θ)   =
  rvl (renameᵗ (liftⁿ (revs Θ) ρ) A) ∷ renᴮ ρ ir Θ
renᴮ ρ ir (rvl⋆ ∷ Θ)    = rvl⋆ ∷ renᴮ ρ ir Θ
renᴮ ρ ir (cnc X A ∷ Θ) = cnc (ρ X) (renameᵗ ir A) ∷ renᴮ ρ ir Θ

-- Shifting the conceal reps.  TyWrap grows the interior by ONE fresh variable
-- (the new reveal), so the conceal reps — which live over the WHOLE interior
-- — must be renamed by suc.  Reveal reps are exterior and untouched, so
-- neither face's reveal side moves.
shiftReps : BCtx → BCtx
shiftReps []            = []
shiftReps (rvl A ∷ Θ)   = rvl A ∷ shiftReps Θ
shiftReps (rvl⋆ ∷ Θ)    = rvl⋆ ∷ shiftReps Θ
shiftReps (cnc X A ∷ Θ) = cnc X (renameᵗ suc A) ∷ shiftReps Θ

revs-shiftReps : ∀ Θ → revs (shiftReps Θ) ≡ revs Θ
revs-shiftReps []            = refl
revs-shiftReps (rvl A ∷ Θ)   = cong suc (revs-shiftReps Θ)
revs-shiftReps (rvl⋆ ∷ Θ)    = cong suc (revs-shiftReps Θ)
revs-shiftReps (cnc X A ∷ Θ) = revs-shiftReps Θ

cmax-shiftReps : ∀ Θ → cmax (shiftReps Θ) ≡ cmax Θ
cmax-shiftReps []            = refl
cmax-shiftReps (rvl A ∷ Θ)   = cmax-shiftReps Θ
cmax-shiftReps (rvl⋆ ∷ Θ)    = cmax-shiftReps Θ
cmax-shiftReps (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-shiftReps Θ)

------------------------------------------------------------------------
-- The AMBIENT dual boundary.  Θᵈ = dualᴳ Γ Θ turns the boundary inside out:
-- its exterior is intOf Γ Θ and its interior REBUILDS Γ.  Every REVEAL of Θ
-- becomes a CONCEAL of Θᵈ at its interior index, carrying its EXTERNAL FACE
-- (a Γ-type — the telescopic reveal block must be resolved first, since a
-- conceal rep lives over the dual's interior); every Γ-slot 0 … cmax Θ ∸ 1
-- that Θ dropped becomes a REVEAL of Θᵈ, whose rep is
--
--   * Θ's own conceal rep for that slot, if Θ conceals it;
--   * otherwise the slot is BLOCKED, and the dual COPIES Γ's own entry —
--     a `rvld B` becomes a reveal at B, an `abst` becomes the REP-LESS
--     reveal rvl⋆.  This is what keeps the rebuild exact: dualᵇ, which
--     invented a dummy rep at every blocked slot, lost the knowledge and
--     broke preservation (notes/old/AmbientDualProbe.agda §3, §5).
--
-- Both kinds of rep must be transported into the dual's TELESCOPIC reveal
-- block: at slot i there are k = cmax Θ ∸ suc i deeper dual reveals below,
-- so a rep over the dual's exterior shifts up by k, and a Γ↓i-relative
-- knowledge rep keeps its first k indices (they name the deeper rebuilt
-- slots) and shifts the rest by revs Θ (the kept part of the exterior).
------------------------------------------------------------------------

repOf : ℕ → BCtx → Ty            -- the rep Θ conceals slot i at (`ℕ if none)
repOf i []            = `ℕ
repOf i (rvl A ∷ Θ)   = repOf i Θ
repOf i (rvl⋆ ∷ Θ)    = repOf i Θ
repOf i (cnc X A ∷ Θ) with i ≟ X
repOf i (cnc X A ∷ Θ) | yes _ = A
repOf i (cnc X A ∷ Θ) | no  _ = repOf i Θ

entAt : TCtx → ℕ → TyEntry       -- Γ's entry at slot i (abst if none)
entAt []      i       = abst
entAt (E ∷ Γ) zero    = E
entAt (E ∷ Γ) (suc i) = entAt Γ i

upFrom : ℕ → ℕ → ℕ → ℕ           -- identity below k, shift by n above
upFrom k n j with j <? k
upFrom k n j | yes _ = j
upFrom k n j | no  _ = n + j

entᴳ : TCtx → BCtx → ℕ → ℕ → BEntry   -- Γ, Θ, slot i, deeper dual reveals k
entᴳ Γ Θ i k with isConc i Θ
entᴳ Γ Θ i k | true  = rvl (renameᵗ (k +_) (repOf i Θ))
entᴳ Γ Θ i k | false with entAt Γ i
entᴳ Γ Θ i k | false | abst   = rvl⋆
entᴳ Γ Θ i k | false | rvld B = rvl (renameᵗ (upFrom k (revs Θ)) B)

rvlsᴳ : ℕ → ℕ → TCtx → BCtx → BCtx    -- k reveals, for dropped slots s, s+1, …
rvlsᴳ zero    s Γ Θ = []
rvlsᴳ (suc k) s Γ Θ = entᴳ Γ Θ s k ∷ rvlsᴳ k (suc s) Γ Θ

cncOfRevs : ℕ → BCtx → BCtx      -- conceal each reveal var, at j, j+1, …
cncOfRevs j []            = []
cncOfRevs j (rvl A ∷ Θ)   =
  cnc j (substᵗ (ρᵇ Θ) A) ∷ cncOfRevs (suc j) Θ
cncOfRevs j (rvl⋆ ∷ Θ)    = cnc j `ℕ ∷ cncOfRevs (suc j) Θ
cncOfRevs j (cnc X A ∷ Θ) = cncOfRevs j Θ

dualᴳ : TCtx → BCtx → BCtx
dualᴳ Γ Θ = rvlsᴳ (cmax Θ) 0 Γ Θ ++ cncOfRevs 0 Θ

-- The two boundary frames hold the same slots in a different order:
-- [reveals of Θ][dropped Γ-slots][kept Γ-slots] becomes
-- [dropped Γ-slots][reveals of Θ][kept Γ-slots], so a boundary type read
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
  renameᵀ (intRen ρ Θ) M
  ⟪ renᴮ ρ (intRen ρ Θ) Θ , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫

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
-- Reduction.  Γ-INDEXED: the index is the type context in which the redex
-- sits, exactly the Δ of the typing judgement, and only Wrap consults it.
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : TCtx → Term → Term → Set where

  -- TyBeta: a boundary is BORN.  The ∀-body B is recorded as the BOUNDARY type;
  -- internal type = B[γ] = B, external type = B[ρ] = B[A]ᵗ.
  TyBeta : Value V
      → Δ ⊢ (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫

  -- Beta
  Beta : Value W
      → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- R1: a wrapped Λ meets a TYPE APPLICATION (the DIRECT-COMBINE form —
  -- notes/DECISIONS.md, Decision 2 as revised).  The elimination CONSUMES the
  -- Λ: the Λ-binder's slot IS the new reveal slot, so the type argument A is
  -- RECORDED as that reveal's rep — never pushed inward, which is what made
  -- the old design unsound (Example 8: A may name a variable the interior
  -- blocks).  There is NO ⇑ᵀ on the term (the design's no-term-shift
  -- principle: a shift forgets which variables a term may not mention); the
  -- CONCEAL REPS do shift, but they are types, and they must, since they live
  -- over the whole interior, which gains the new reveal's variable
  -- (shiftReps).  The new reveal is the SHALLOWEST one, and under the
  -- TELESCOPIC reading of the reveal block a reveal's rep is read over the
  -- exterior extended by the DEEPER reveals, so the type argument A — a
  -- plain exterior type — is lifted past them; its external face is A again
  -- (ρᵇ-lift).  Partial by design: a wrapper-bodied wrapper at a ∀ face is
  -- a Merge redex (Decision 3), not a TyWrap redex.
  TyWrap : Value V
      → Δ ⊢ ((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ V ⟪ rvl (renameᵗ (revs Θ +_) A) ∷ shiftReps Θ , B₀ ⟫

  -- R2: a wrapped ƛ meets an APPLICATION.  Symmetric to TyWrap: the
  -- elimination CONSUMES the ƛ and β-substitutes in one step.  The argument
  -- lives in the EXTERIOR, so it is moved inside through the AMBIENT DUAL
  -- first; _[_]ᵐ is TERM-variable substitution only, so again no term shift
  -- is involved.  B₁ is read over Θ's boundary frame, so the dual's boundary
  -- type is B₁ renamed by the frame permutation swapᵇ.  This is the ONE rule
  -- that reads the ambient Δ: the dual copies Δ's own entry at every slot Θ
  -- drops without concealing.
  Wrap : Value W
      → Δ ⊢ ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
        -→ (N [ W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ]ᵐ) ⟪ Θ , B₂ ⟫

  -- ξ (congruence): the evaluation frames, left-to-right call-by-value.
  -- ξ-Λ and ξ-⟪⟫ are not optional bookkeeping: Λ V is a value only when V is
  -- (G-Λ) and V ⟪ Θ , B₀ ⟫ only when V is (V-⟪⟫), so the body of a Λ and the
  -- interior of a boundary must be reduced in place before either is a value
  -- — and each carries the index INTO the sub-term's own context.
  ξ-·-l : Δ ⊢ L -→ L′
        → Δ ⊢ L · M -→ L′ · M

  ξ-·-r : Value V → Δ ⊢ M -→ M′
        → Δ ⊢ V · M -→ V · M′

  ξ-·[] : Δ ⊢ L -→ L′
        → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]

  ξ-Λ   : (abst ∷ Δ) ⊢ N -→ N′
        → Δ ⊢ Λ N -→ Λ N′

  ξ-⟪⟫  : intOf Δ Θ ⊢ M -→ M′
        → Δ ⊢ M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- Worked example:  (ΛX. λx:X.x) [X→X, ℕ]  →  (λx:X.x)⟪↑X:=ℕ⟫   (both : ℕ→ℕ)
------------------------------------------------------------------------

⊢redex-Λ : [] ∣ [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢redex-Λ = ⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) wf-ℕ

_ : [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫
_ = TyBeta (V-G G-ƛ)

⊢contractum-Λ :
  [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢contractum-Λ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                    (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Beta:  (λx:ℕ. x) · 5  →  5    (both : ℕ)
------------------------------------------------------------------------

⊢redex-ƛ : [] ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) ⦂ `ℕ
⊢redex-ƛ = ⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$

_ : [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) -→ $ 5
_ = Beta V-$

⊢contractum-ƛ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
⊢contractum-ƛ = ⊢$

------------------------------------------------------------------------
-- Worked example for ξ-⟪⟫:  reduce the INTERIOR of a reveal boundary.
--   ((λx:ℕ. x) · 5) ⟪ ↑X:=ℕ , B₀=ℕ ⟫  →  5 ⟪ ↑X:=ℕ , B₀=ℕ ⟫   (both : ℕ)
-- The interior context is  X:=ℕ ∣ []  (one reveal, no conceal); B₀ = ℕ has
-- no free variable, so both faces are ℕ: the boundary is inert on the type.
------------------------------------------------------------------------

⊢redex-bnd : [] ∣ [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢redex-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ (⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$)

_ : [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
    -→ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
_ = ξ-⟪⟫ (Beta V-$)

⊢contractum-bnd : [] ∣ [] ⊢ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ ⊢$

------------------------------------------------------------------------
-- Worked example for TyWrap (R1), on the NEW-DESIGN ANALOGUE OF EXAMPLE 8.
-- Example 8 (notes/old/Scratch7-9) is the closed program whose 4th step
-- made the OLD design ill-typed: a value concealed on X (index 1) is
-- TYPE-APPLIED to
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
-- Δ8 must now KNOW X (the reversal premise licenses a conceal only against
-- the exterior's own knowledge), so X is revealed at ℕ and Y is Λ-bound.
------------------------------------------------------------------------

polyid : Term
polyid = Λ (ƛ ` 0 ∙ ` 0)

Δ8 : TCtx                     -- Y (Λ-bound, index 0), X:=ℕ (index 1)
Δ8 = abst ∷ rvld `ℕ ∷ []

Θ8 : BCtx                       -- conceal X (index 1), rep ℕ
Θ8 = cnc 1 `ℕ ∷ []

_ : intOf Δ8 Θ8 ≡ []
_ = refl

_ : baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []          -- Y is BLOCKED inside
_ = refl

⊢redex-R1 : Δ8 ∣ [] ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                      ⦂ (` 0 ⇒ ` 0)
⊢redex-R1 =
  ⊢·[] (env (bwf↓ (skip-abst here) refl wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-abst)

-- polyid is Λ (ƛ ` 0 ∙ ` 0), so the rule's Value premise is the Λ-BODY's:
-- V-G G-ƛ, not the whole polyid's V-G (G-Λ …)
_ : Δ8 ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
_ = TyWrap (V-G G-ƛ)

-- the new reveal's rep is the BLOCKED Y, so its interior entry is `abst`
_ : intOf Δ8 (rvl (` 0) ∷ shiftReps Θ8) ≡ abst ∷ []
_ = refl

⊢contractum-R1 :
  Δ8 ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1 =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here) refl wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Worked example for TyWrap where the LIFT bites: the boundary already
-- REVEALS, so the type argument X must move past that reveal slot to
-- become the shallowest reveal's telescopic rep.
--
--   Δt = X:=𝔹            Θt = ↑Z:=ℕ            (revs Θt = 1)
--   ((ΛW. λw:W. w) ⟪ Θt , ∀(W→W) ⟫) ·[ W→W , X ]      : X→X
--     →  (λw:W. w) ⟪ ↑W:=(the lift of X) , ↑Z:=ℕ , W→W ⟫
--
-- The new reveal's rep is ` 1, which is X read over the frame of the tail
-- [↑Z:=ℕ] ++ Δt — and its interior entry is the KNOWLEDGE W:=` 1, the
-- interior slot of X read over the entry's own tail.
------------------------------------------------------------------------

Δt : TCtx
Δt = rvld `𝔹 ∷ []

Θt : BCtx
Θt = rvl `ℕ ∷ []

_ : intOf Δt Θt ≡ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

⊢redex-R1t : Δt ∣ [] ⊢ (polyid ⟪ Θt , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                       ⦂ (` 0 ⇒ ` 0)
⊢redex-R1t =
  ⊢·[] (env (bwf↑ wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-rvld)

_ : Δt ⊢ (polyid ⟪ Θt , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 1) ∷ rvl `ℕ ∷ [] , ` 0 ⇒ ` 0 ⟫
_ = TyWrap (V-G G-ƛ)

-- the new reveal's external face is the type argument again …
_ : ρᵇ (rvl (` 1) ∷ rvl `ℕ ∷ []) 0 ≡ ` 0
_ = refl

-- … and its interior entry is X's interior slot, read over its own tail
_ : intOf Δt (rvl (` 1) ∷ rvl `ℕ ∷ [])
    ≡ rvld (` 1) ∷ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

⊢contractum-R1t :
  Δt ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 1) ∷ rvl `ℕ ∷ [] , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1t =
  env (bwf↑ (wf-var (skip-abst here-rvld)) (bwf↑ wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Wrap (R2), on a MIXED boundary — one reveal AND one
-- conceal, the shape R1 produces (⊢contractum-R1 above), and the case a
-- "restrict R2 to cmax Θ = 0" design would not cover.
--
--   ((λz:Z. z) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z→Z ⟫) · 3                        : ℕ
--     →  (3 ⟪ dualᴳ Δm Θm , X ⟫) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z ⟫             : ℕ
--
-- The ƛ is consumed and its body ` 0 is substituted for, so the contractum is
-- the dual-wrapped argument under the original boundary.
--
-- Exterior Δm = [Y , X:=ℕ]; the interior is [Z:=ℕ] and Y is BLOCKED there.
-- The AMBIENT dual is [↑⋆ , ↑ℕ , ↓Z:=ℕ]: the blocked Y is Λ-BOUND in Δm, so
-- the dual re-introduces it with the REP-LESS reveal (dualᵇ used to invent
-- the knowledge Y:=ℕ there), X comes back at its conceal rep, and the reveal
-- variable Z is concealed at its external face.  swapᵇ Θm sends Θm's frame
-- [Z , Y , X] slot 0 (Z) to slot 2 of the dual's frame [X , Y , Z], so the
-- dual's boundary type is ` 2.
------------------------------------------------------------------------

Δm : TCtx                       -- Y (Λ-bound, index 0), X:=ℕ (index 1)
Δm = abst ∷ rvld `ℕ ∷ []

Θm : BCtx                       -- reveal Z:=ℕ, conceal X (index 1)
Θm = rvl `ℕ ∷ cnc 1 `ℕ ∷ []

_ : intOf Δm Θm ≡ rvld `ℕ ∷ []
_ = refl

_ : baseS Θm Δm ≡ ok ∷ blk ∷ ok ∷ []          -- Y is blocked
_ = refl

_ : dualᴳ Δm Θm ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- the dual's interior is Δm ON THE NOSE (the rep-less reveal rebuilds the
-- Λ-bound Y as abstract, which is exactly Δm's entry)
_ : intOf (intOf Δm Θm) (dualᴳ Δm Θm) ≡ Δm
_ = refl

_ : swapᵇ Θm 0 ≡ 2
_ = refl

⊢redex-R2m : Δm ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3) ⦂ `ℕ
⊢redex-R2m =
  ⊢· (env (bwf↑ wf-ℕ (bwf↓ (skip-abst here) refl wf-ℕ bwf[]))
          (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
          (⊢ƛ (wf-var here-rvld) (⊢` here)))
     ⊢$

-- the ƛ's body is ` 0, so N [ … ]ᵐ IS the wrapped argument (definitionally)
_ : Δm ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3)
    -→ (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫
_ = Wrap V-$

⊢contractum-R2m :
  Δm ∣ [] ⊢ (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫ ⦂ `ℕ
⊢contractum-R2m =
  env (bwf↑ wf-ℕ (bwf↓ (skip-abst here) refl wf-ℕ bwf[]))
      (sc-var hereᵒ)
      (env (bwf⋆ (bwf↑ wf-ℕ (bwf↓ here refl wf-ℕ bwf[])))
           (sc-var (thereᵒ (thereᵒ hereᵒ)))
           ⊢$)

------------------------------------------------------------------------
-- The CHAINED-KNOWLEDGE dual (notes/old/AmbientDualProbe.agda §6b, the residue
-- (R1) that forced the telescopic reveal block).  Γp = Y:=Y′ , Y′:=𝔹 , X:=ℕ
-- is reachable — TyBeta turns a Λ-bound Y into Y:=Y′ without renaming — and
-- Θp = ↓X:=ℕ drops all three.  The copied entry for Y names Y′, which the
-- boundary also drops; under the PARALLEL reading of a reveal block that rep
-- was ill formed.  Telescopically it is exactly the right entry, and the
-- rebuild is Γp on the nose.
------------------------------------------------------------------------

Γp : TCtx                       -- Y:=Y′ , Y′:=𝔹 , X:=ℕ
Γp = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

Θp : BCtx
Θp = cnc 2 `ℕ ∷ []

_ : dualᴳ Γp Θp ≡ rvl (` 0) ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

_ : intOf Γp Θp ≡ []
_ = refl

-- WELL FORMED (the probe's ¬⊢dualᴳΓp is refuted by the telescopic reading)
⊢dualᴳΓp : [] ∣ intOf [] (dualᴳ Γp Θp) ⊢ᵇ dualᴳ Γp Θp
⊢dualᴳΓp = bwf↑ (wf-var here-abst) (bwf↑ wf-𝔹 (bwf↑ wf-ℕ bwf[]))

-- … and it rebuilds Γp exactly
_ : intOf (intOf Γp Θp) (dualᴳ Γp Θp) ≡ Γp
_ = refl

------------------------------------------------------------------------
-- renameᵀ through a boundary, verified on ⇑ᵀ of the non-spurious ($7)⟪Θ₈, X⟫.
-- Under ⇑ᵀ (new abstract W at Γ-index 0):  conceal index 1 ↦ 2, reveal rep ` 0
-- (=Y) ↦ ` 1, B₀ = X = ` 2 ↦ ` 3 (bframe lift), body 7 unchanged (the
-- conceal absorbs the shift, so intRen = id).
------------------------------------------------------------------------

_ : ⇑ᵀ (($ 7) ⟪ Θ₈ , ` 2 ⟫) ≡ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫
_ = refl

-- ⊢renameᵀ on this instance: the renamed wrapper types at abst ∷ Γ₈ with the
-- renamed external type ` 2 (= renameᵗ suc of the original external ` 1 = X).
-- The conceal's reversal premise moves with it: both sides are still ℕ.
_ : (abst ∷ Γ₈) ∣ [] ⊢ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫ ⦂ ` 2
_ = env (bwf↓ (skip-abst (skip-abst here)) refl wf-ℕ
             (bwf↑ (wf-var (skip-abst here-abst)) bwf[]))
        (sc-var (thereᵒ (thereᵒ (thereᵒ hereᵒ)))) ⊢$

------------------------------------------------------------------------
-- Type-variable renaming preserves typing  (⊢renameᵀ)
------------------------------------------------------------------------

∋-map : ∀ {ρ} {Γₜ : Ctx} {x A}
      → Γₜ ∋ x ⦂ A → map (renameᵗ ρ) Γₜ ∋ x ⦂ renameᵗ ρ A
∋-map here      = here
∋-map (there p) = there (∋-map p)

wf-ren : ∀ {ρ Δ Δ'} {A : Ty}
       → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Δ ⊢ A → Δ' ⊢ renameᵗ ρ A
wf-ren h wfA = wf-rename-fv (λ y → h (fv-scope wfA y)) wfA

ext-h : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
      → (∀ {X} → (abst ∷ Δ) ∋tv X → (abst ∷ Δ') ∋tv extᵗ ρ X)
ext-h h here-abst    = here-abst
ext-h h (skip-abst p) = skip-abst (h p)

⤊-ren : ∀ {ρ} (Γₜ : Ctx)
      → map (renameᵗ (extᵗ ρ)) (⤊ Γₜ) ≡ ⤊ (map (renameᵗ ρ) Γₜ)
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
-- external commutation: renaming commutes with the external projection ρᵇ.
-- With the TELESCOPIC reveal block this is no longer a plain lookup: at a
-- reveal slot both sides substitute the tail's own external face into the
-- rep, so the induction hypothesis is used at every index of the rep.
------------------------------------------------------------------------

ρᵇ-comm : ∀ ρ ir Θ X
        → ρᵇ (renᴮ ρ ir Θ) (liftⁿ (revs Θ) ρ X) ≡ renameᵗ ρ (ρᵇ Θ X)
ρᵇ-comm ρ ir []            X       = refl
ρᵇ-comm ρ ir (rvl A ∷ Θ)   zero    =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ) (ρᵇ (renᴮ ρ ir Θ)) A)
    (trans (subst-cong (ρᵇ-comm ρ ir Θ) A)
           (sym (rename-subst ρ (ρᵇ Θ) A)))
ρᵇ-comm ρ ir (rvl A ∷ Θ)   (suc Y) = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (rvl⋆ ∷ Θ)    zero    = refl
ρᵇ-comm ρ ir (rvl⋆ ∷ Θ)    (suc Y) = ρᵇ-comm ρ ir Θ Y
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
-- renᴮ keeps the reveal count and the reveal KINDS, and (for a Mono ρ)
-- sends the deepest conceal index X to ρ X — so cmax has one of two shapes
-- after renaming.
------------------------------------------------------------------------

revs-ren : ∀ ρ ir Θ → revs (renᴮ ρ ir Θ) ≡ revs Θ
revs-ren ρ ir []            = refl
revs-ren ρ ir (rvl A ∷ Θ)   = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (rvl⋆ ∷ Θ)    = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (cnc X A ∷ Θ) = revs-ren ρ ir Θ

revSlots-ren : ∀ ρ ir Θ → revSlots (renᴮ ρ ir Θ) ≡ revSlots Θ
revSlots-ren ρ ir []            = refl
revSlots-ren ρ ir (rvl A ∷ Θ)   = cong (ok ∷_) (revSlots-ren ρ ir Θ)
revSlots-ren ρ ir (rvl⋆ ∷ Θ)    = cong (blk ∷_) (revSlots-ren ρ ir Θ)
revSlots-ren ρ ir (cnc X A ∷ Θ) = revSlots-ren ρ ir Θ

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
cmax-ren mono ir (rvl⋆ ∷ Θ) with cmax-ren mono ir Θ
cmax-ren mono ir (rvl⋆ ∷ Θ) | cm-0 e e'   = cm-0 e e'
cmax-ren mono ir (rvl⋆ ∷ Θ) | cm-s Y e e' = cm-s Y e e'
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-0 e e' =
  cm-s X (cong (λ n → suc X ⊔ n) e) (cong (λ n → suc (ρ X) ⊔ n) e')
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-s Y e e' =
  cm-s (X ⊔ Y) (cong (λ n → suc X ⊔ n) e)
       (trans (cong (λ n → suc (ρ X) ⊔ n) e')
              (cong suc (sym (⊔-mono-comm mono X Y))))

------------------------------------------------------------------------
-- Decidable/Bool plumbing for isConc (whose cons case is ⌊ i ≟ X ⌋ ∨ …).
------------------------------------------------------------------------

⌊⌋-true : ∀ {P : Set} (d : Dec P) → ⌊ d ⌋ ≡ true → P
⌊⌋-true (yes p) _  = p
⌊⌋-true (no ¬p) ()

⌊⌋-of : ∀ {P : Set} (d : Dec P) → P → ⌊ d ⌋ ≡ true
⌊⌋-of (yes _) _ = refl
⌊⌋-of (no ¬p) p = ⊥-elim (¬p p)

⌊⌋-false : ∀ {P : Set} (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
⌊⌋-false (yes p) ¬p = ⊥-elim (¬p p)
⌊⌋-false (no  _) _  = refl

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
isConc-ren ρ ir (rvl⋆ ∷ Θ)    i c = isConc-ren ρ ir Θ i c
isConc-ren ρ ir (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₁ p =
  isConc-here (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) (cong ρ p)
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ)
               (isConc-ren ρ ir Θ i t)

-- … and, since ρ is injective, ONLY a concealed one does
isConc-ren-inv : ∀ {ρ} → Mono ρ → ∀ ir Θ i
               → isConc (ρ i) (renᴮ ρ ir Θ) ≡ true → isConc i Θ ≡ true
isConc-ren-inv mono ir []            i ()
isConc-ren-inv mono ir (rvl A ∷ Θ)   i c = isConc-ren-inv mono ir Θ i c
isConc-ren-inv mono ir (rvl⋆ ∷ Θ)    i c = isConc-ren-inv mono ir Θ i c
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c
  with isConc-cons (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) c
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c | inj₁ q =
  isConc-here i X A Θ (Mono→inj mono q)
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there i X A Θ (isConc-ren-inv mono ir Θ i t)

------------------------------------------------------------------------
-- The accessibility bridge: baseS Θ Δ ∋ok (revs Θ + i) says exactly that
-- i is a KEPT (cmax Θ ≤ i) or CONCEALED index of Δ — the two cases where
-- γcnc commutes with renaming.  Both directions are needed.  The reveal
-- prefix is now PER ENTRY (revSlots), a rep-less reveal being blocked.
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

revS-drop : ∀ Θ {Ψ i} → (revSlots Θ ++ Ψ) ∋ok (revs Θ + i) → Ψ ∋ok i
revS-drop []            p = p
revS-drop (rvl A ∷ Θ)   p = revS-drop Θ (∋ok-tail p)
revS-drop (rvl⋆ ∷ Θ)    p = revS-drop Θ (∋ok-tail p)
revS-drop (cnc X A ∷ Θ) p = revS-drop Θ p

revS-add : ∀ Θ {Ψ i} → Ψ ∋ok i → (revSlots Θ ++ Ψ) ∋ok (revs Θ + i)
revS-add []            p = p
revS-add (rvl A ∷ Θ)   p = thereᵒ (revS-add Θ p)
revS-add (rvl⋆ ∷ Θ)    p = thereᵒ (revS-add Θ p)
revS-add (cnc X A ∷ Θ) p = revS-add Θ p

-- a reveal slot that IS accessible stays accessible whatever follows it
revS-lo : ∀ Θ {Ψ Ψ'} X → X < revs Θ
        → (revSlots Θ ++ Ψ) ∋ok X → (revSlots Θ ++ Ψ') ∋ok X
revS-lo []            X       ()       p
revS-lo (rvl A ∷ Θ)   zero    lt       p = hereᵒ
revS-lo (rvl A ∷ Θ)   (suc X) (s≤s lt) p =
  thereᵒ (revS-lo Θ X lt (∋ok-tail p))
revS-lo (rvl⋆ ∷ Θ)    zero    lt       p =
  ⊥-elim (ok≢blk (sym (∋ok-head p)))
revS-lo (rvl⋆ ∷ Θ)    (suc X) (s≤s lt) p =
  thereᵒ (revS-lo Θ X lt (∋ok-tail p))
revS-lo (cnc Y A ∷ Θ) X       lt       p = revS-lo Θ X lt p

-- transport of a reveal slot along a boundary renaming (revSlots is stable)
revS-≡ : ∀ Θ Θ' {Ψ Ψ'} → revSlots Θ ≡ revSlots Θ' → ∀ X → X < revs Θ
       → (revSlots Θ ++ Ψ) ∋ok X → (revSlots Θ' ++ Ψ') ∋ok X
revS-≡ Θ Θ' {Ψ} {Ψ'} e X lt p =
  subst (λ S → (S ++ Ψ') ∋ok X) e (revS-lo Θ X lt p)

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
  acc-of Θ i (slotsᴳ-ok Θ Δ 0 i (revS-drop Θ p))

baseS-∋tv : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i) → Δ ∋tv i
baseS-∋tv {Δ} Θ i p = slotsᴳ-∋tv Θ Δ 0 i (revS-drop Θ p)

baseS-ok : ∀ {Δ} Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → Δ ∋tv i
         → baseS Θ Δ ∋ok (revs Θ + i)
baseS-ok {Δ} Θ i acc q =
  revS-add Θ (slotsᴳ-add Θ Δ 0 i q (acc-slotAt Θ i acc))

------------------------------------------------------------------------
-- Internal commutation.  The deep part of γᵇ is γcnc, which commutes
-- with ρ at kept and concealed indices (it does NOT at blocked ones —
-- that is exactly what the (env) scope premise rules out).
------------------------------------------------------------------------

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
γcnc-comm {ρ} mono r m m' (rvl⋆ ∷ Θ) i hyp acc =
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
-- THE REVERSAL PREMISE TRANSPORTS.  outSub is built from ρᵇ, which commutes
-- with renaming at EVERY slot (ρᵇ-comm) — no scope restriction, the point of
-- the reversal form (notes/old/ReversalProbe.agda §5).
------------------------------------------------------------------------

outSub-lo : ∀ Θ X → X < revs Θ → outSub Θ X ≡ ρᵇ Θ X
outSub-lo Θ X lt with X <? revs Θ
outSub-lo Θ X lt | yes _  = refl
outSub-lo Θ X lt | no ¬lt = ⊥-elim (¬lt lt)

outSub-hi : ∀ Θ X → ¬ (X < revs Θ)
          → outSub Θ X ≡ ` (cmax Θ + (X ∸ revs Θ))
outSub-hi Θ X ¬lt with X <? revs Θ
outSub-hi Θ X ¬lt | yes lt = ⊥-elim (¬lt lt)
outSub-hi Θ X ¬lt | no  _  = refl

outSub-ren : ∀ {ρ} → Mono ρ → ∀ Θ X
  → outSub (renᴮ ρ (intRen ρ Θ) Θ) (intRen ρ Θ X)
    ≡ renameᵗ ρ (outSub Θ X)
outSub-ren {ρ} mono Θ X with split (revs Θ) X
outSub-ren {ρ} mono Θ X | inj₁ lt =
  trans (cong (outSub Θ′) (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) X lt))
    (trans (outSub-lo Θ′ X (subst (X <_) (sym (revs-ren ρ ir Θ)) lt))
      (trans (cong (ρᵇ Θ′) (sym (liftⁿ-lo (revs Θ) ρ X lt)))
        (trans (ρᵇ-comm ρ ir Θ X)
               (cong (renameᵗ ρ) (sym (outSub-lo Θ X lt))))))
  where ir = intRen ρ Θ
        Θ′ = renᴮ ρ (intRen ρ Θ) Θ
outSub-ren {ρ} mono Θ .(revs Θ + i) | inj₂ (i , refl) =
  trans (cong (outSub Θ′) (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) i))
    (trans (outSub-hi Θ′ (revs Θ + d)
             (λ lt → m+n≮m (revs Θ) d
                       (subst (revs Θ + d <_) (revs-ren ρ ir Θ) lt)))
      (trans (cong (λ n → ` (cmax Θ′ + n))
                   (trans (cong (revs Θ + d ∸_) (revs-ren ρ ir Θ))
                          (m+n∸m≡n (revs Θ) d)))
        (trans (cong `_ (key mono))
               (cong (renameᵗ ρ)
                 (sym (trans (outSub-hi Θ (revs Θ + i)
                        (m+n≮m (revs Θ) i))
                      (cong (λ n → ` (cmax Θ + n))
                            (m+n∸m≡n (revs Θ) i))))))))
  where
    ir = intRen ρ Θ
    Θ′ = renᴮ ρ (intRen ρ Θ) Θ
    d  = deepRen (cmax Θ) ρ i
    key : Mono ρ → cmax Θ′ + d ≡ ρ (cmax Θ + i)
    key mo with cmax-ren {ρ} mo ir Θ
    key mo | cm-0 e e′ rewrite e | e′ = refl
    key mo | cm-s Y e e′ rewrite e | e′ =
      m+[n∸m]≡n (mo {Y} {suc Y + i} (m≤m+n (suc Y) i))

Reversal-ren : ∀ {ρ} → Mono ρ → ∀ Θ X A A₀
  → Reversal Θ X A A₀
  → Reversal (renᴮ ρ (intRen ρ Θ) Θ) (ρ X)
             (renameᵗ (intRen ρ Θ) A) (renameᵗ (restrictRen X ρ) A₀)
Reversal-ren {ρ} mono Θ X A A₀ h =
  trans (rename-subst-commute (intRen ρ Θ) (outSub Θ′) A)
    (trans (subst-cong (λ Y → outSub-ren mono Θ Y) A)
      (trans (sym (rename-subst ρ (outSub Θ) A))
        (trans (cong (renameᵗ ρ) h)
          (trans (rename-rename-commute (λ i → suc X + i) ρ A₀)
            (trans (rename-cong eq A₀)
                   (sym (rename-rename-commute (restrictRen X ρ)
                          (λ i → suc (ρ X) + i) A₀)))))))
  where
    Θ′ = renᴮ ρ (intRen ρ Θ) Θ
    eq : ∀ i → ρ (suc X + i) ≡ suc (ρ X) + restrictRen X ρ i
    eq i = sym (m+[n∸m]≡n (mono {X} {suc X + i} (m≤m+n (suc X) i)))

------------------------------------------------------------------------
-- The interior context transports: intOf Δ Θ → intOf Δ' (renᴮ … Θ).
-- Lookup ignores the abst/rvld marker, so only the SHAPE of the reveal
-- block matters here (len-revEnts); the knowledge the entries carry is the
-- business of ∋:=-int below.
------------------------------------------------------------------------

∋tv-≡ : ∀ {Γ Γ' Z Z'} → Γ ≡ Γ' → Z ≡ Z' → Γ ∋tv Z → Γ' ∋tv Z'
∋tv-≡ refl refl p = p

ent-here : ∀ (E : TyEntry) (Γ : TCtx) → (E ∷ Γ) ∋tv zero
ent-here abst     Γ = here-abst
ent-here (rvld A) Γ = here-rvld

ent-skip : ∀ (E : TyEntry) {Γ Y} → Γ ∋tv Y → (E ∷ Γ) ∋tv suc Y
ent-skip abst     p = skip-abst p
ent-skip (rvld A) p = skip-rvld p

revE-lo : ∀ Θ j Ξ {Γ : TCtx} Y → Y < revs Ξ → (revEnts Θ j Ξ ++ Γ) ∋tv Y
revE-lo Θ j []            Y       ()
revE-lo Θ j (rvl A ∷ Ξ)   zero    lt = ent-here (⟦ Θ ⟧ᵉ j (revs Ξ) A) _
revE-lo Θ j (rvl A ∷ Ξ)   (suc Y) (s≤s lt) =
  ent-skip (⟦ Θ ⟧ᵉ j (revs Ξ) A) (revE-lo Θ (suc j) Ξ Y lt)
revE-lo Θ j (rvl⋆ ∷ Ξ)    zero    lt = here-abst
revE-lo Θ j (rvl⋆ ∷ Ξ)    (suc Y) (s≤s lt) =
  skip-abst (revE-lo Θ (suc j) Ξ Y lt)
revE-lo Θ j (cnc X A ∷ Ξ) Y       lt = revE-lo Θ j Ξ Y lt

revE-hi : ∀ Θ j Ξ {Γ : TCtx} {Z} → Γ ∋tv Z
        → (revEnts Θ j Ξ ++ Γ) ∋tv (revs Ξ + Z)
revE-hi Θ j []            p = p
revE-hi Θ j (rvl A ∷ Ξ)   p =
  ent-skip (⟦ Θ ⟧ᵉ j (revs Ξ) A) (revE-hi Θ (suc j) Ξ p)
revE-hi Θ j (rvl⋆ ∷ Ξ)    p = skip-abst (revE-hi Θ (suc j) Ξ p)
revE-hi Θ j (cnc X A ∷ Ξ) p = revE-hi Θ j Ξ p

revE-hi⁻ : ∀ Θ j Ξ {Γ : TCtx} {Z} → (revEnts Θ j Ξ ++ Γ) ∋tv (revs Ξ + Z)
         → Γ ∋tv Z
revE-hi⁻ Θ j []            p = p
revE-hi⁻ Θ j (rvl A ∷ Ξ)   p = revE-hi⁻ Θ (suc j) Ξ (∋tv-tail p)
revE-hi⁻ Θ j (rvl⋆ ∷ Ξ)    p = revE-hi⁻ Θ (suc j) Ξ (∋tv-tail p)
revE-hi⁻ Θ j (cnc X A ∷ Ξ) p = revE-hi⁻ Θ j Ξ p

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
  ∋tv-≡ refl (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
        (revE-lo Θ' 0 Θ' Y
          (subst (Y <_) (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₂ (Z , refl) =
  ∋tv-≡ refl
        (trans (cong (_+ deepRen (cmax Θ) ρ Z)
                     (revs-ren ρ (intRen ρ Θ) Θ))
               (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z)))
        (revE-hi Θ' 0 Θ'
          (drop-int h mono Θ (revE-hi⁻ Θ 0 Θ p)))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ

------------------------------------------------------------------------
-- The (env) scope premise transports.
------------------------------------------------------------------------

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
        (revS-≡ Θ (renᴮ ρ (intRen ρ Θ) Θ)
                (sym (revSlots-ren ρ (intRen ρ Θ) Θ)) X lt okp)
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

------------------------------------------------------------------------
-- Boundary well-formedness transports.  The reveal premise lives over the
-- exterior extended by the DEEPER reveals, so it renames by liftⁿ; the
-- conceal premise needs BOTH the exterior's knowledge transport (∋:=) and
-- Reversal-ren.
------------------------------------------------------------------------

h-prep : ∀ {ρ Δ Δ'} r → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
       → ∀ {Y} → prepAbst r Δ ∋tv Y → prepAbst r Δ' ∋tv liftⁿ r ρ Y
h-prep {ρ} {Δ} {Δ'} r h {Y} p with split r Y
h-prep {ρ} {Δ} {Δ'} r h {Y} p | inj₁ lt =
  ∋tv-≡ refl (sym (liftⁿ-lo r ρ Y lt)) (prepAbst-lo r Δ' Y lt)
  where
    prepAbst-lo : ∀ r (Γ : TCtx) Y → Y < r → prepAbst r Γ ∋tv Y
    prepAbst-lo zero    Γ Y       ()
    prepAbst-lo (suc r) Γ zero    _         = here-abst
    prepAbst-lo (suc r) Γ (suc Y) (s≤s Y<r) =
      skip-abst (prepAbst-lo r Γ Y Y<r)
h-prep {ρ} {Δ} {Δ'} r h {Y} p | inj₂ (Z , refl) =
  ∋tv-≡ refl (sym (liftⁿ-hi r ρ Z)) (pa-hi r Δ' (h (pa-hi⁻ r Δ Z p)))
  where
    pa-hi : ∀ r (Γ : TCtx) {Z} → Γ ∋tv Z → prepAbst r Γ ∋tv (r + Z)
    pa-hi zero    Γ p = p
    pa-hi (suc r) Γ p = skip-abst (pa-hi r Γ p)
    pa-hi⁻ : ∀ r (Γ : TCtx) Z → prepAbst r Γ ∋tv (r + Z) → Γ ∋tv Z
    pa-hi⁻ zero    Γ Z p             = p
    pa-hi⁻ (suc r) Γ Z (skip-abst p) = pa-hi⁻ r Γ Z p

prepAbst-lo : ∀ r (Γ : TCtx) Y → Y < r → prepAbst r Γ ∋tv Y
prepAbst-lo zero    Γ Y       ()
prepAbst-lo (suc r) Γ zero    _         = here-abst
prepAbst-lo (suc r) Γ (suc Y) (s≤s Y<r) =
  skip-abst (prepAbst-lo r Γ Y Y<r)

prepAbst-hi : ∀ r (Γ : TCtx) Z → Γ ∋tv Z → prepAbst r Γ ∋tv (r + Z)
prepAbst-hi zero    Γ Z p = p
prepAbst-hi (suc r) Γ Z p = skip-abst (prepAbst-hi r Γ Z p)

bwf-ren : ∀ {ρ Δ Δ' Ψ Ψ' Θ Ξ} → Mono ρ
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → (∀ {Y} → Ψ ∋tv Y → Ψ' ∋tv intRen ρ Θ Y)
  → Bwf Δ Ψ Θ Ξ
  → Bwf Δ' Ψ' (renᴮ ρ (intRen ρ Θ) Θ) (renᴮ ρ (intRen ρ Θ) Ξ)
bwf-ren mono h hk hi bwf[] = bwf[]
bwf-ren {ρ} {Θ = Θ} mono h hk hi (bwf↑ {A} {Ξ} wfA b) =
  bwf↑ (subst (λ r → prepAbst r _ ⊢ renameᵗ (liftⁿ (revs Ξ) ρ) A)
              (sym (revs-ren ρ (intRen ρ Θ) Ξ))
              (wf-ren (h-prep (revs Ξ) h) wfA))
       (bwf-ren mono h hk hi b)
bwf-ren mono h hk hi (bwf⋆ b) = bwf⋆ (bwf-ren mono h hk hi b)
bwf-ren {ρ} {Θ = Θ} mono h hk hi (bwf↓ {X} {A} {A₀} p rev wfA b) =
  bwf↓ (hk p) (Reversal-ren mono Θ X A A₀ rev)
       (wf-ren hi wfA) (bwf-ren mono h hk hi b)

------------------------------------------------------------------------
-- Retagging.  Typing now READS the abst/rvld marker (a conceal is licensed
-- against the exterior's knowledge), so a derivation no longer transports
-- along a context of the same LENGTH.  It transports along Δ ≼ Δ′ —
-- entrywise, `abst` below anything and a knowledge entry below itself —
-- which is exactly what the ambient dual's rebuild delivers.
------------------------------------------------------------------------

infix 4 _≼_
data _≼_ : TCtx → TCtx → Set where
  ≼[]   : [] ≼ []
  ≼abst : ∀ {Δ Δ' E} → Δ ≼ Δ' → (abst ∷ Δ) ≼ (E ∷ Δ')
  ≼rvld : ∀ {Δ Δ' A} → Δ ≼ Δ' → (rvld A ∷ Δ) ≼ (rvld A ∷ Δ')

≼-refl : ∀ (Δ : TCtx) → Δ ≼ Δ
≼-refl []            = ≼[]
≼-refl (abst ∷ Δ)    = ≼abst (≼-refl Δ)
≼-refl (rvld A ∷ Δ)  = ≼rvld (≼-refl Δ)

≼-len : ∀ {Δ Δ'} → Δ ≼ Δ' → length Δ ≡ length Δ'
≼-len ≼[]        = refl
≼-len (≼abst p)  = cong suc (≼-len p)
≼-len (≼rvld p)  = cong suc (≼-len p)

≼-∋tv : ∀ {Δ Δ' X} → Δ ≼ Δ' → Δ ∋tv X → Δ' ∋tv X
≼-∋tv (≼abst {E = abst}   p) here-abst     = here-abst
≼-∋tv (≼abst {E = rvld A} p) here-abst     = here-rvld
≼-∋tv (≼rvld p)              here-rvld     = here-rvld
≼-∋tv (≼abst {E = abst}   p) (skip-abst q) = skip-abst (≼-∋tv p q)
≼-∋tv (≼abst {E = rvld A} p) (skip-abst q) = skip-rvld (≼-∋tv p q)
≼-∋tv (≼rvld p)              (skip-rvld q) = skip-rvld (≼-∋tv p q)

≼-∋:= : ∀ {Δ Δ' X A} → Δ ≼ Δ' → Δ ∋ X := A → Δ' ∋ X := A
≼-∋:= (≼rvld p)              here          = here
≼-∋:= (≼abst {E = abst}   p) (skip-abst q) = skip-abst (≼-∋:= p q)
≼-∋:= (≼abst {E = rvld A} p) (skip-abst q) = skip-rvld (≼-∋:= p q)
≼-∋:= (≼rvld p)              (skip-rvld q) = skip-rvld (≼-∋:= p q)

≼-⊢ : ∀ {Δ Δ' A} → Δ ≼ Δ' → Δ ⊢ A → Δ' ⊢ A
≼-⊢ p (wf-var q) = wf-var (≼-∋tv p q)
≼-⊢ p wf-ℕ       = wf-ℕ
≼-⊢ p wf-𝔹       = wf-𝔹
≼-⊢ p (wf-⇒ a b) = wf-⇒ (≼-⊢ p a) (≼-⊢ p b)
≼-⊢ p (wf-∀ a)   = wf-∀ (≼-⊢ (≼abst p) a)

≼-dropN : ∀ c {Δ Δ'} → Δ ≼ Δ' → dropN c Δ ≼ dropN c Δ'
≼-dropN zero    p           = p
≼-dropN (suc c) ≼[]         = ≼[]
≼-dropN (suc c) (≼abst p)   = ≼-dropN c p
≼-dropN (suc c) (≼rvld p)   = ≼-dropN c p

≼-prepAbst : ∀ r {Δ Δ'} → Δ ≼ Δ' → prepAbst r Δ ≼ prepAbst r Δ'
≼-prepAbst zero    p = p
≼-prepAbst (suc r) p = ≼abst (≼-prepAbst r p)

≼-app : ∀ (Ψ₀ : TCtx) {Δ Δ'} → Δ ≼ Δ' → (Ψ₀ ++ Δ) ≼ (Ψ₀ ++ Δ')
≼-app []            p = p
≼-app (abst ∷ Ψ₀)   p = ≼abst (≼-app Ψ₀ p)
≼-app (rvld A ∷ Ψ₀) p = ≼rvld (≼-app Ψ₀ p)

≼-intOf : ∀ Θ {Δ Δ'} → Δ ≼ Δ' → intOf Δ Θ ≼ intOf Δ' Θ
≼-intOf Θ p = ≼-app (revEnts Θ 0 Θ) (≼-dropN (cmax Θ) p)

bwf-retag : ∀ {Δ Δ' Ψ Ψ' Θ Ξ} → Δ ≼ Δ' → Ψ ≼ Ψ'
          → Bwf Δ Ψ Θ Ξ → Bwf Δ' Ψ' Θ Ξ
bwf-retag pΔ pΨ bwf[]              = bwf[]
bwf-retag pΔ pΨ (bwf↑ {Ξ = Ξ} wfA b) =
  bwf↑ (≼-⊢ (≼-prepAbst (revs Ξ) pΔ) wfA) (bwf-retag pΔ pΨ b)
bwf-retag pΔ pΨ (bwf⋆ b)           = bwf⋆ (bwf-retag pΔ pΨ b)
bwf-retag pΔ pΨ (bwf↓ p rev wfA b) =
  bwf↓ (≼-∋:= pΔ p) rev (≼-⊢ pΨ wfA) (bwf-retag pΔ pΨ b)

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
  cong (revSlots Θ ++_) (slotsᴳ-len Θ 0 Γ Γ' le)

⊢retag : ∀ {Δ Δ' Γₜ M A} → Δ ≼ Δ'
       → Δ ∣ Γₜ ⊢ M ⦂ A → Δ' ∣ Γₜ ⊢ M ⦂ A
⊢retag p (⊢` q)        = ⊢` q
⊢retag p ⊢$            = ⊢$
⊢retag p (⊢ƛ wfA ⊢N)   = ⊢ƛ (≼-⊢ p wfA) (⊢retag p ⊢N)
⊢retag p (⊢· ⊢L ⊢M)    = ⊢· (⊢retag p ⊢L) (⊢retag p ⊢M)
⊢retag p (⊢Λ ⊢N)       = ⊢Λ (⊢retag (≼abst p) ⊢N)
⊢retag p (⊢·[] ⊢L wfA) = ⊢·[] (⊢retag p ⊢L) (≼-⊢ p wfA)
⊢retag {Δ} {Δ'} p (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) =
  env (bwf-retag p (≼-intOf Θ p) bwf)
      (subst (λ Ψ → Scoped Ψ B₀) (baseS-len Θ Δ Δ' (≼-len p)) sc)
      (⊢retag (≼-intOf Θ p) ⊢M)

------------------------------------------------------------------------
-- Boundary shift (R1).  The face laws of  rvl A′ ∷ shiftReps Θ  — the
-- boundary TyWrap builds, whose new reveal is the SHALLOWEST one, so its
-- rep A′ is the type argument A LIFTED past the boundary's existing
-- reveals (the telescopic reading; a type shift, not a term shift).  The
-- interior face becomes extsᵗ of the old one AT EVERY SLOT (blocked ones
-- included), so R1 carries no scope side-condition of its own; the
-- exterior face instantiates the ∀ with the type argument A.
------------------------------------------------------------------------

isConc-shift : ∀ i Θ → isConc i (shiftReps Θ) ≡ isConc i Θ
isConc-shift i []            = refl
isConc-shift i (rvl A ∷ Θ)   = isConc-shift i Θ
isConc-shift i (rvl⋆ ∷ Θ)    = isConc-shift i Θ
isConc-shift i (cnc X A ∷ Θ) = cong (⌊ i ≟ X ⌋ ∨_) (isConc-shift i Θ)

-- shiftReps does not move the reveals, so the EXTERIOR face is untouched
ρᵇ-shift : ∀ Θ X → ρᵇ (shiftReps Θ) X ≡ ρᵇ Θ X
ρᵇ-shift []            X       = refl
ρᵇ-shift (rvl A ∷ Θ)   zero    = subst-cong (ρᵇ-shift Θ) A
ρᵇ-shift (rvl A ∷ Θ)   (suc X) = ρᵇ-shift Θ X
ρᵇ-shift (rvl⋆ ∷ Θ)    zero    = refl
ρᵇ-shift (rvl⋆ ∷ Θ)    (suc X) = ρᵇ-shift Θ X
ρᵇ-shift (cnc X A ∷ Θ) Y       = ρᵇ-shift Θ Y

γcnc-shift : ∀ r m Θ i
  → γcnc (suc r) m (shiftReps Θ) i ≡ renameᵗ suc (γcnc r m Θ i)
γcnc-shift r m []            i = refl
γcnc-shift r m (rvl A ∷ Θ)   i = γcnc-shift r m Θ i
γcnc-shift r m (rvl⋆ ∷ Θ)    i = γcnc-shift r m Θ i
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

-- the exterior face is the identity on the Γ-part of the boundary frame
ρᵇ-hi : ∀ Θ i → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-hi []            i = refl
ρᵇ-hi (rvl A ∷ Θ)   i = ρᵇ-hi Θ i
ρᵇ-hi (rvl⋆ ∷ Θ)    i = ρᵇ-hi Θ i
ρᵇ-hi (cnc X A ∷ Θ) i = ρᵇ-hi Θ i

-- the LIFTED type argument reads back as itself: the new reveal's external
-- face is exactly A
ρᵇ-lift : ∀ Θ A → substᵗ (ρᵇ Θ) (renameᵗ (revs Θ +_) A) ≡ A
ρᵇ-lift Θ A =
  trans (rename-subst-commute (revs Θ +_) (ρᵇ Θ) A)
        (trans (subst-cong (ρᵇ-hi Θ) A) (subst-id A))

-- FACE LAW (exterior).  The new reveal instantiates the ∀ with A.
ρᵇ-shift-ty : ∀ A Θ B
  → substᵗ (ρᵇ (rvl (renameᵗ (revs Θ +_) A) ∷ shiftReps Θ)) B
    ≡ (substᵗ (extsᵗ (ρᵇ Θ)) B) [ A ]ᵗ
ρᵇ-shift-ty A Θ B =
  trans (subst-cong h B) (sym (exts-sub-cons {σ = ρᵇ Θ} {a = B} {v = A}))
  where
    h : ∀ X → ρᵇ (rvl (renameᵗ (revs Θ +_) A) ∷ shiftReps Θ) X
            ≡ cons-sub A (ρᵇ Θ) X
    h zero    =
      trans (subst-cong (ρᵇ-shift Θ) (renameᵗ (revs Θ +_) A))
            (ρᵇ-lift Θ A)
    h (suc X) = ρᵇ-shift Θ X

-- the reversal premise survives the shift: the conceal reps move by suc and
-- the read-back map is unchanged
-- an opaque decision, so that `with` does not unfold outSub in the goal
dec-< : ∀ a b → (a < b) ⊎ (¬ (a < b))
dec-< a b with a <? b
dec-< a b | yes p  = inj₁ p
dec-< a b | no ¬p  = inj₂ ¬p

outSub-shift : ∀ A Θ k
  → outSub (rvl A ∷ shiftReps Θ) (suc k) ≡ outSub Θ k
outSub-shift A Θ k with dec-< k (revs Θ)
outSub-shift A Θ k | inj₁ lt =
  trans (outSub-lo (rvl A ∷ shiftReps Θ) (suc k) lt')
    (trans (ρᵇ-shift Θ k) (sym (outSub-lo Θ k lt)))
  where lt' : suc k < revs (rvl A ∷ shiftReps Θ)
        lt' = subst (λ n → suc k < suc n) (sym (revs-shiftReps Θ)) (s≤s lt)
outSub-shift A Θ k | inj₂ ¬lt =
  trans (outSub-hi (rvl A ∷ shiftReps Θ) (suc k) ¬lt')
    (trans (cong₂ (λ c r → ` (c + (k ∸ r)))
                  (cmax-shiftReps Θ) (revs-shiftReps Θ))
           (sym (outSub-hi Θ k ¬lt)))
  where ¬lt' : ¬ (suc k < revs (rvl A ∷ shiftReps Θ))
        ¬lt' q = ¬lt (subst (λ n → k < n) (revs-shiftReps Θ)
                            (≤-pred′ q))
          where ≤-pred′ : suc k < suc (revs (shiftReps Θ))
                        → k < revs (shiftReps Θ)
                ≤-pred′ (s≤s r) = r

Reversal-shift : ∀ A Θ X T A₀ → Reversal Θ X T A₀
               → Reversal (rvl A ∷ shiftReps Θ) X (renameᵗ suc T) A₀
Reversal-shift A Θ X T A₀ h =
  trans (rename-subst-commute suc (outSub (rvl A ∷ shiftReps Θ)) T)
        (trans (subst-cong (outSub-shift A Θ) T) h)

-- an arbitrary entry weakens a well-formed type
wf-⇑ : ∀ {Δ A} (E : TyEntry) → Δ ⊢ A → (E ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑ E wfA = wf-rename-fv (λ y → ent-skip E (fv-scope wfA y)) wfA

-- the boundary stays well formed once the interior gains one variable
bwf-shiftReps : ∀ {Δ Ψ A} (E : TyEntry) Θ Ξ → Bwf Δ Ψ Θ Ξ
  → Bwf Δ (E ∷ Ψ) (rvl A ∷ shiftReps Θ) (shiftReps Ξ)
bwf-shiftReps E Θ []            bwf[]              = bwf[]
bwf-shiftReps E Θ (rvl B ∷ Ξ)   (bwf↑ wfB b)       =
  bwf↑ (subst (λ r → prepAbst r _ ⊢ B) (sym (revs-shiftReps Ξ)) wfB)
       (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps E Θ (rvl⋆ ∷ Ξ)    (bwf⋆ b)           =
  bwf⋆ (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps {A = A} E Θ (cnc X B ∷ Ξ) (bwf↓ {A₀ = A₀} p rev wfB b) =
  bwf↓ p (Reversal-shift A Θ X B A₀ rev) (wf-⇑ E wfB)
       (bwf-shiftReps E Θ Ξ b)

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

revSlots-shift : ∀ Θ → revSlots (shiftReps Θ) ≡ revSlots Θ
revSlots-shift []            = refl
revSlots-shift (rvl A ∷ Θ)   = cong (ok ∷_) (revSlots-shift Θ)
revSlots-shift (rvl⋆ ∷ Θ)    = cong (blk ∷_) (revSlots-shift Θ)
revSlots-shift (cnc X A ∷ Θ) = revSlots-shift Θ

baseS-shift : ∀ A Θ (Γ : TCtx)
  → baseS (rvl A ∷ shiftReps Θ) Γ ≡ ok ∷ baseS Θ Γ
baseS-shift A Θ Γ =
  cong (ok ∷_)
    (cong₂ _++_ (revSlots-shift Θ) (slotsᴳ-shift A Θ 0 Γ))

-- the lift really is needed: over a boundary that already reveals, the type
-- argument moves past the existing reveal slots and its external face is
-- itself again
_ : ρᵇ (rvl (renameᵗ (revs (rvl `ℕ ∷ []) +_) (` 0)) ∷ rvl `ℕ ∷ []) 0
    ≡ ` 0
_ = refl

------------------------------------------------------------------------
-- Dual boundary, part 1: the SHAPE of dualᴳ.  Its reveal block is the
-- Γ-prefix Θ drops (so revs Θᵈ = cmax Θ) and its conceal block is Θ's own
-- reveals (so cmax Θᵈ = revs Θ) — the two blocks of the frame swap.  Every
-- entry the reveal block produces IS a reveal (with or without a rep), which
-- is all the shape lemmas need to know about entᴳ.
------------------------------------------------------------------------

data RvlE : BEntry → Set where
  is-rvl : ∀ {A} → RvlE (rvl A)
  is-⋆   : RvlE rvl⋆

entᴳ-RvlE : ∀ Γ Θ i k → RvlE (entᴳ Γ Θ i k)
entᴳ-RvlE Γ Θ i k with isConc i Θ
entᴳ-RvlE Γ Θ i k | true  = is-rvl
entᴳ-RvlE Γ Θ i k | false with entAt Γ i
entᴳ-RvlE Γ Θ i k | false | abst   = is-⋆
entᴳ-RvlE Γ Θ i k | false | rvld B = is-rvl

revs-R : ∀ {E} → RvlE E → ∀ Ξ → revs (E ∷ Ξ) ≡ suc (revs Ξ)
revs-R is-rvl Ξ = refl
revs-R is-⋆   Ξ = refl

cmax-R : ∀ {E} → RvlE E → ∀ Ξ → cmax (E ∷ Ξ) ≡ cmax Ξ
cmax-R is-rvl Ξ = refl
cmax-R is-⋆   Ξ = refl

isConc-R : ∀ {E} → RvlE E → ∀ Ξ i → isConc i (E ∷ Ξ) ≡ isConc i Ξ
isConc-R is-rvl Ξ i = refl
isConc-R is-⋆   Ξ i = refl

ρᵇ-R-suc : ∀ {E} → RvlE E → ∀ Ξ n → ρᵇ (E ∷ Ξ) (suc n) ≡ ρᵇ Ξ n
ρᵇ-R-suc is-rvl Ξ n = refl
ρᵇ-R-suc is-⋆   Ξ n = refl

γcnc-R : ∀ {E} → RvlE E → ∀ r m Ξ i → γcnc r m (E ∷ Ξ) i ≡ γcnc r m Ξ i
γcnc-R is-rvl r m Ξ i = refl
γcnc-R is-⋆   r m Ξ i = refl

revS-R-suc : ∀ {E} → RvlE E → ∀ Ξ (S : SCtx) i
           → (revSlots Ξ ++ S) ∋ok i → (revSlots (E ∷ Ξ) ++ S) ∋ok suc i
revS-R-suc is-rvl Ξ S i p = thereᵒ p
revS-R-suc is-⋆   Ξ S i p = thereᵒ p

revs-++ : ∀ Θ₁ Θ₂ → revs (Θ₁ ++ Θ₂) ≡ revs Θ₁ + revs Θ₂
revs-++ []            Θ₂ = refl
revs-++ (rvl A ∷ Θ₁)  Θ₂ = cong suc (revs-++ Θ₁ Θ₂)
revs-++ (rvl⋆ ∷ Θ₁)   Θ₂ = cong suc (revs-++ Θ₁ Θ₂)
revs-++ (cnc X A ∷ Θ₁) Θ₂ = revs-++ Θ₁ Θ₂

cmax-++ : ∀ Θ₁ Θ₂ → cmax (Θ₁ ++ Θ₂) ≡ cmax Θ₁ ⊔ cmax Θ₂
cmax-++ []            Θ₂ = refl
cmax-++ (rvl A ∷ Θ₁)  Θ₂ = cmax-++ Θ₁ Θ₂
cmax-++ (rvl⋆ ∷ Θ₁)   Θ₂ = cmax-++ Θ₁ Θ₂
cmax-++ (cnc X A ∷ Θ₁) Θ₂ =
  trans (cong (suc X ⊔_) (cmax-++ Θ₁ Θ₂))
        (sym (⊔-assoc (suc X) (cmax Θ₁) (cmax Θ₂)))

revs-rvlsᴳ : ∀ k s Γ Θ → revs (rvlsᴳ k s Γ Θ) ≡ k
revs-rvlsᴳ zero    s Γ Θ = refl
revs-rvlsᴳ (suc k) s Γ Θ =
  trans (revs-R (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ))
        (cong suc (revs-rvlsᴳ k (suc s) Γ Θ))

cmax-rvlsᴳ : ∀ k s Γ Θ → cmax (rvlsᴳ k s Γ Θ) ≡ 0
cmax-rvlsᴳ zero    s Γ Θ = refl
cmax-rvlsᴳ (suc k) s Γ Θ =
  trans (cmax-R (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ))
        (cmax-rvlsᴳ k (suc s) Γ Θ)

revs-cncOfRevs : ∀ j Θ → revs (cncOfRevs j Θ) ≡ 0
revs-cncOfRevs j []            = refl
revs-cncOfRevs j (rvl A ∷ Θ)   = revs-cncOfRevs (suc j) Θ
revs-cncOfRevs j (rvl⋆ ∷ Θ)    = revs-cncOfRevs (suc j) Θ
revs-cncOfRevs j (cnc X A ∷ Θ) = revs-cncOfRevs j Θ

-- the conceals sit at j … j + revs Θ ∸ 1, so the deepest is j + revs Θ
-- (and there is none at all when Θ has no reveal) — stated ⊔ j to cover
-- both shapes at once
cmax-cncOfRevs : ∀ j Θ → cmax (cncOfRevs j Θ) ⊔ j ≡ j + revs Θ
cmax-cncOfRevs j []            = sym (+-identityʳ j)
cmax-cncOfRevs j (rvl A ∷ Θ)   =
  trans (m≥n⇒m⊔n≡m (≤-trans (n≤1+n j)
                            (m≤m⊔n (suc j) (cmax (cncOfRevs (suc j) Θ)))))
    (trans (⊔-comm (suc j) (cmax (cncOfRevs (suc j) Θ)))
      (trans (cmax-cncOfRevs (suc j) Θ) (sym (+-suc j (revs Θ)))))
cmax-cncOfRevs j (rvl⋆ ∷ Θ)    =
  trans (m≥n⇒m⊔n≡m (≤-trans (n≤1+n j)
                            (m≤m⊔n (suc j) (cmax (cncOfRevs (suc j) Θ)))))
    (trans (⊔-comm (suc j) (cmax (cncOfRevs (suc j) Θ)))
      (trans (cmax-cncOfRevs (suc j) Θ) (sym (+-suc j (revs Θ)))))
cmax-cncOfRevs j (cnc X A ∷ Θ) = cmax-cncOfRevs j Θ

cmax-cncOfRevs0 : ∀ Θ → cmax (cncOfRevs 0 Θ) ≡ revs Θ
cmax-cncOfRevs0 Θ =
  trans (sym (⊔-identityʳ (cmax (cncOfRevs 0 Θ)))) (cmax-cncOfRevs 0 Θ)

revs-dual : ∀ Γ Θ → revs (dualᴳ Γ Θ) ≡ cmax Θ
revs-dual Γ Θ =
  trans (revs-++ (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong₂ _+_ (revs-rvlsᴳ (cmax Θ) 0 Γ Θ) (revs-cncOfRevs 0 Θ))
           (+-identityʳ (cmax Θ)))

cmax-dual : ∀ Γ Θ → cmax (dualᴳ Γ Θ) ≡ revs Θ
cmax-dual Γ Θ =
  trans (cmax-++ (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong (_⊔ cmax (cncOfRevs 0 Θ)) (cmax-rvlsᴳ (cmax Θ) 0 Γ Θ))
           (cmax-cncOfRevs0 Θ))

------------------------------------------------------------------------
-- Part 2: the two FACE laws.  On Θ's boundary frame the slot X is sent by
-- swapᵇ to the slot of Θᵈ's frame holding the same variable, and there
--   ρᵇ Θᵈ ∘ swapᵇ Θ = γᵇ Θ    (at ACCESSIBLE slots only)
--   γᵇ Θᵈ ∘ swapᵇ Θ = ρᵇ Θ    (at every slot)
-- The first fails at a blocked slot — the dual re-introduces it from the
-- AMBIENT context while γᵇ aliases it onto a kept variable — which is why
-- R2 goes through subst-cong-sc with (env)'s scope premise.
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
isConc-< []            i ()
isConc-< (rvl A ∷ Θ)   i c = isConc-< Θ i c
isConc-< (rvl⋆ ∷ Θ)    i c = isConc-< Θ i c
isConc-< (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-< (cnc X A ∷ Θ) i c | inj₁ refl = m≤m⊔n (suc i) (cmax Θ)
isConc-< (cnc X A ∷ Θ) i c | inj₂ t =
  ≤-trans (isConc-< Θ i t) (m≤n⊔m (suc X) (cmax Θ))

-- the interior face at a Γ-slot: a concealed one goes to its rep, a kept
-- one to its interior slot
γcnc-conc : ∀ r m Θ i → isConc i Θ ≡ true → γcnc r m Θ i ≡ repOf i Θ
γcnc-conc r m []            i ()
γcnc-conc r m (rvl A ∷ Θ)   i c = γcnc-conc r m Θ i c
γcnc-conc r m (rvl⋆ ∷ Θ)    i c = γcnc-conc r m Θ i c
γcnc-conc r m (cnc X A ∷ Θ) i c with X ≟ i | i ≟ X
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | yes q = refl
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | no ¬q = ⊥-elim (¬q (sym p))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | yes q = ⊥-elim (¬p (sym q))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | no ¬q = γcnc-conc r m Θ i c

γcnc-kept : ∀ r m Θ i → cmax Θ ≤ i → γcnc r m Θ i ≡ ` (r + (i ∸ m))
γcnc-kept r m []            i le = refl
γcnc-kept r m (rvl A ∷ Θ)   i le = γcnc-kept r m Θ i le
γcnc-kept r m (rvl⋆ ∷ Θ)    i le = γcnc-kept r m Θ i le
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

-- the exterior face of the DUAL: its reveal block resolves the dropped
-- slots, and everything above it passes through
ρᵇ-cncOfRevs : ∀ j Θ i → ρᵇ (cncOfRevs j Θ) i ≡ ` i
ρᵇ-cncOfRevs j []            i = refl
ρᵇ-cncOfRevs j (rvl A ∷ Θ)   i = ρᵇ-cncOfRevs (suc j) Θ i
ρᵇ-cncOfRevs j (rvl⋆ ∷ Θ)    i = ρᵇ-cncOfRevs (suc j) Θ i
ρᵇ-cncOfRevs j (cnc X A ∷ Θ) i = ρᵇ-cncOfRevs j Θ i

ρᵇ-rvlsᴳ-hi : ∀ k s Γ Θ Ξ j → ρᵇ (rvlsᴳ k s Γ Θ ++ Ξ) (k + j) ≡ ρᵇ Ξ j
ρᵇ-rvlsᴳ-hi zero    s Γ Θ Ξ j = refl
ρᵇ-rvlsᴳ-hi (suc k) s Γ Θ Ξ j =
  trans (ρᵇ-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ Ξ) (k + j))
        (ρᵇ-rvlsᴳ-hi k (suc s) Γ Θ Ξ j)

ρᵇ-dual-hi : ∀ Γ Θ k → ρᵇ (dualᴳ Γ Θ) (cmax Θ + k) ≡ ` k
ρᵇ-dual-hi Γ Θ k =
  trans (ρᵇ-rvlsᴳ-hi (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
        (ρᵇ-cncOfRevs 0 Θ k)

-- at a CONCEALED slot the dual's reveal carries Θ's own conceal rep, shifted
-- past the deeper dual reveals; resolving the telescope gives it back
ρᵇ-ent-conc : ∀ Γ Θ s k (Ξ : BCtx) → isConc s Θ ≡ true
  → (∀ m → ρᵇ Ξ (k + m) ≡ ` m)
  → ρᵇ (entᴳ Γ Θ s k ∷ Ξ) zero ≡ repOf s Θ
ρᵇ-ent-conc Γ Θ s k Ξ c h with isConc s Θ | c
ρᵇ-ent-conc Γ Θ s k Ξ c h | true  | _ =
  trans (rename-subst-commute (k +_) (ρᵇ Ξ) (repOf s Θ))
        (trans (subst-cong h (repOf s Θ)) (subst-id (repOf s Θ)))
ρᵇ-ent-conc Γ Θ s k Ξ c h | false | ()

ρᵇ-rvlsᴳ-conc : ∀ k s Γ Θ i → i < k → isConc (s + i) Θ ≡ true
  → ρᵇ (rvlsᴳ k s Γ Θ ++ cncOfRevs 0 Θ) i ≡ repOf (s + i) Θ
ρᵇ-rvlsᴳ-conc zero    s Γ Θ i       ()       c
ρᵇ-rvlsᴳ-conc (suc k) s Γ Θ zero    lt       c =
  trans (ρᵇ-ent-conc Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ cncOfRevs 0 Θ)
          (trans (cong (λ n → isConc n Θ) (sym (+-identityʳ s))) c)
          (λ m → trans (ρᵇ-rvlsᴳ-hi k (suc s) Γ Θ (cncOfRevs 0 Θ) m)
                       (ρᵇ-cncOfRevs 0 Θ m)))
        (cong (λ n → repOf n Θ) (sym (+-identityʳ s)))
ρᵇ-rvlsᴳ-conc (suc k) s Γ Θ (suc i) (s≤s lt) c =
  trans (ρᵇ-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ cncOfRevs 0 Θ)
                  i)
        (trans (ρᵇ-rvlsᴳ-conc k (suc s) Γ Θ i lt
                 (trans (cong (λ n → isConc n Θ) (sym (+-suc s i))) c))
               (cong (λ n → repOf n Θ) (sym (+-suc s i))))

ρᵇ-dual-lo : ∀ Γ Θ i → i < cmax Θ → isConc i Θ ≡ true
           → ρᵇ (dualᴳ Γ Θ) i ≡ repOf i Θ
ρᵇ-dual-lo Γ Θ i lt c = ρᵇ-rvlsᴳ-conc (cmax Θ) 0 Γ Θ i lt c

-- the interior face of the DUAL: its conceal block resolves Θ's reveal
-- variables to Θ's own EXTERNAL faces, and everything above it is kept
γcnc-rvlsᴳ : ∀ r m k s Γ Θ Ξ i
  → γcnc r m (rvlsᴳ k s Γ Θ ++ Ξ) i ≡ γcnc r m Ξ i
γcnc-rvlsᴳ r m zero    s Γ Θ Ξ i = refl
γcnc-rvlsᴳ r m (suc k) s Γ Θ Ξ i =
  trans (γcnc-R (entᴳ-RvlE Γ Θ s k) r m
                (rvlsᴳ k (suc s) Γ Θ ++ Ξ) i)
        (γcnc-rvlsᴳ r m k (suc s) Γ Θ Ξ i)

γcnc-cnc-lo : ∀ r m j Θ k → k < revs Θ
  → γcnc r m (cncOfRevs j Θ) (j + k) ≡ ρᵇ Θ k
γcnc-cnc-lo r m j []            k       ()
γcnc-cnc-lo r m j (rvl A ∷ Θ)   zero    lt =
  sover-hit j (substᵗ (ρᵇ Θ) A) (γcnc r m (cncOfRevs (suc j) Θ)) (j + 0)
            (sym (+-identityʳ j))
γcnc-cnc-lo r m j (rvl A ∷ Θ)   (suc k) (s≤s lt) =
  trans (sover-miss j (substᵗ (ρᵇ Θ) A)
                    (γcnc r m (cncOfRevs (suc j) Θ)) (j + suc k)
                    (j≢j+suc j k))
    (trans (cong (γcnc r m (cncOfRevs (suc j) Θ)) (+-suc j k))
           (γcnc-cnc-lo r m (suc j) Θ k lt))
γcnc-cnc-lo r m j (rvl⋆ ∷ Θ)    zero    lt =
  sover-hit j `ℕ (γcnc r m (cncOfRevs (suc j) Θ)) (j + 0)
            (sym (+-identityʳ j))
γcnc-cnc-lo r m j (rvl⋆ ∷ Θ)    (suc k) (s≤s lt) =
  trans (sover-miss j `ℕ (γcnc r m (cncOfRevs (suc j) Θ)) (j + suc k)
                    (j≢j+suc j k))
    (trans (cong (γcnc r m (cncOfRevs (suc j) Θ)) (+-suc j k))
           (γcnc-cnc-lo r m (suc j) Θ k lt))
γcnc-cnc-lo r m j (cnc X A ∷ Θ) k       lt = γcnc-cnc-lo r m j Θ k lt

γcnc-cnc-hi : ∀ r m j Θ i → j + revs Θ ≤ i
  → γcnc r m (cncOfRevs j Θ) i ≡ ` (r + (i ∸ m))
γcnc-cnc-hi r m j []            i le = refl
γcnc-cnc-hi r m j (rvl A ∷ Θ)   i le =
  trans (sover-miss j (substᵗ (ρᵇ Θ) A)
                    (γcnc r m (cncOfRevs (suc j) Θ)) i ne)
        (γcnc-cnc-hi r m (suc j) Θ i le')
  where
    le' : suc j + revs Θ ≤ i
    le' = subst (_≤ i) (+-suc j (revs Θ)) le
    ne : ¬ (j ≡ i)
    ne p = <-irrefl p (≤-trans (s≤s (m≤m+n j (revs Θ))) le')
γcnc-cnc-hi r m j (rvl⋆ ∷ Θ)    i le =
  trans (sover-miss j `ℕ (γcnc r m (cncOfRevs (suc j) Θ)) i ne)
        (γcnc-cnc-hi r m (suc j) Θ i le')
  where
    le' : suc j + revs Θ ≤ i
    le' = subst (_≤ i) (+-suc j (revs Θ)) le
    ne : ¬ (j ≡ i)
    ne p = <-irrefl p (≤-trans (s≤s (m≤m+n j (revs Θ))) le')
γcnc-cnc-hi r m j (cnc X A ∷ Θ) i le = γcnc-cnc-hi r m j Θ i le

γᵇ-dual-lo : ∀ Γ Θ i → i < cmax Θ → γᵇ (dualᴳ Γ Θ) i ≡ ` i
γᵇ-dual-lo Γ Θ i lt =
  prepId-lo (revs (dualᴳ Γ Θ))
            (γcnc (revs (dualᴳ Γ Θ)) (cmax (dualᴳ Γ Θ)) (dualᴳ Γ Θ)) i
            (subst (i <_) (sym (revs-dual Γ Θ)) lt)

γᵇ-dual-hi : ∀ Γ Θ k
  → γᵇ (dualᴳ Γ Θ) (cmax Θ + k)
    ≡ γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k
γᵇ-dual-hi Γ Θ k =
  trans (prepId-hi′ (cmax Θ) (revs (dualᴳ Γ Θ))
                    (γcnc (revs (dualᴳ Γ Θ)) (cmax (dualᴳ Γ Θ))
                          (dualᴳ Γ Θ)) k
                    (revs-dual Γ Θ))
        (cong₂ (λ a b → γcnc a b (dualᴳ Γ Θ) k)
               (revs-dual Γ Θ) (cmax-dual Γ Θ))

γcnc-dual-lo : ∀ Γ Θ k → k < revs Θ
  → γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k ≡ ρᵇ Θ k
γcnc-dual-lo Γ Θ k lt =
  trans (γcnc-rvlsᴳ (cmax Θ) (revs Θ) (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
        (γcnc-cnc-lo (cmax Θ) (revs Θ) 0 Θ k lt)

γcnc-dual-hi : ∀ Γ Θ k → revs Θ ≤ k
  → γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k ≡ ` (cmax Θ + (k ∸ revs Θ))
γcnc-dual-hi Γ Θ k le =
  trans (γcnc-rvlsᴳ (cmax Θ) (revs Θ) (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
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
ρᵇ-dual-swap : ∀ {Δ} Γ Θ X → baseS Θ Δ ∋ok X
             → ρᵇ (dualᴳ Γ Θ) (swapᵇ Θ X) ≡ γᵇ Θ X
ρᵇ-dual-swap Γ Θ X okp with split (revs Θ) X
ρᵇ-dual-swap Γ Θ X okp | inj₁ lt =
  trans (cong (ρᵇ (dualᴳ Γ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
    (trans (ρᵇ-dual-hi Γ Θ X)
           (sym (prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X lt)))
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl)
  with baseS-acc Θ i okp
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  trans (cong (ρᵇ (dualᴳ Γ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (ρᵇ-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ)))
           (sym (γᵇ-kept Θ i le)))
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  trans (cong (ρᵇ (dualᴳ Γ Θ))
              (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
    (trans (ρᵇ-dual-lo Γ Θ i (isConc-< Θ i cc) cc) (sym (γᵇ-conc Θ i cc)))

-- FACE LAW (interior of the dual = exterior of Θ), at EVERY slot
γᵇ-dual-swap : ∀ Γ Θ X → γᵇ (dualᴳ Γ Θ) (swapᵇ Θ X) ≡ ρᵇ Θ X
γᵇ-dual-swap Γ Θ X with split (revs Θ) X
γᵇ-dual-swap Γ Θ X | inj₁ lt =
  trans (cong (γᵇ (dualᴳ Γ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
        (trans (γᵇ-dual-hi Γ Θ X) (γcnc-dual-lo Γ Θ X lt))
γᵇ-dual-swap Γ Θ .(revs Θ + i) | inj₂ (i , refl) with cmax Θ ≤? i
γᵇ-dual-swap Γ Θ .(revs Θ + i) | inj₂ (i , refl) | yes le =
  trans (cong (γᵇ (dualᴳ Γ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (γᵇ-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ)))
      (trans (γcnc-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ))
                           (m≤m+n (revs Θ) (i ∸ cmax Θ)))
        (trans (cong (λ n → ` (cmax Θ + n))
                     (m+n∸m≡n (revs Θ) (i ∸ cmax Θ)))
          (trans (cong `_ (m+[n∸m]≡n le)) (sym (ρᵇ-hi Θ i))))))
γᵇ-dual-swap Γ Θ .(revs Θ + i) | inj₂ (i , refl) | no ¬le =
  trans (cong (γᵇ (dualᴳ Γ Θ)) (swap-mid (revs Θ) (cmax Θ) i (≰⇒> ¬le)))
        (trans (γᵇ-dual-lo Γ Θ i (≰⇒> ¬le)) (sym (ρᵇ-hi Θ i)))

-- the two face laws as the retypings preservation needs.  The exterior one
-- is scope-restricted (subst-cong-sc with (env)'s premise for B₁).
ρᵇ-dual-ty : ∀ {Δ} Γ B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (ρᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (γᵇ Θ) B
ρᵇ-dual-ty Γ B Θ sc =
  trans (rename-subst-commute (swapᵇ Θ) (ρᵇ (dualᴳ Γ Θ)) B)
        (subst-cong-sc sc (λ X okp → ρᵇ-dual-swap Γ Θ X okp))

γᵇ-dual-ty : ∀ Γ B Θ
  → substᵗ (γᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (ρᵇ Θ) B
γᵇ-dual-ty Γ B Θ =
  trans (rename-subst-commute (swapᵇ Θ) (γᵇ (dualᴳ Γ Θ)) B)
        (subst-cong (γᵇ-dual-swap Γ Θ) B)

------------------------------------------------------------------------
-- Part 3: the dual's frame is all-accessible where it must be.
------------------------------------------------------------------------

isConc-++ʳ : ∀ i Θ₁ Θ₂ → isConc i Θ₂ ≡ true → isConc i (Θ₁ ++ Θ₂) ≡ true
isConc-++ʳ i []            Θ₂ c = c
isConc-++ʳ i (rvl A ∷ Θ₁)  Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c
isConc-++ʳ i (rvl⋆ ∷ Θ₁)   Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c
isConc-++ʳ i (cnc X A ∷ Θ₁) Θ₂ c =
  isConc-there i X A (Θ₁ ++ Θ₂) (isConc-++ʳ i Θ₁ Θ₂ c)

isConc-cncOfRevs : ∀ j Θ k → k < revs Θ
                 → isConc (j + k) (cncOfRevs j Θ) ≡ true
isConc-cncOfRevs j []            k       ()
isConc-cncOfRevs j (rvl A ∷ Θ)   zero    lt =
  isConc-here (j + 0) j (substᵗ (ρᵇ Θ) A) (cncOfRevs (suc j) Θ)
              (+-identityʳ j)
isConc-cncOfRevs j (rvl A ∷ Θ)   (suc k) (s≤s lt) =
  isConc-there (j + suc k) j (substᵗ (ρᵇ Θ) A) (cncOfRevs (suc j) Θ)
    (subst (λ n → isConc n (cncOfRevs (suc j) Θ) ≡ true)
           (sym (+-suc j k)) (isConc-cncOfRevs (suc j) Θ k lt))
isConc-cncOfRevs j (rvl⋆ ∷ Θ)    zero    lt =
  isConc-here (j + 0) j `ℕ (cncOfRevs (suc j) Θ) (+-identityʳ j)
isConc-cncOfRevs j (rvl⋆ ∷ Θ)    (suc k) (s≤s lt) =
  isConc-there (j + suc k) j `ℕ (cncOfRevs (suc j) Θ)
    (subst (λ n → isConc n (cncOfRevs (suc j) Θ) ≡ true)
           (sym (+-suc j k)) (isConc-cncOfRevs (suc j) Θ k lt))
isConc-cncOfRevs j (cnc X A ∷ Θ) k       lt = isConc-cncOfRevs j Θ k lt

isConc-dual : ∀ Γ Θ k → k < revs Θ → isConc k (dualᴳ Γ Θ) ≡ true
isConc-dual Γ Θ k lt =
  isConc-++ʳ k (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ)
             (isConc-cncOfRevs 0 Θ k lt)

dropN-∋tv : ∀ c (Γ : TCtx) i → c ≤ i → Γ ∋tv i → dropN c Γ ∋tv (i ∸ c)
dropN-∋tv zero    Γ       i       le       p = p
dropN-∋tv (suc c) []      i       le       ()
dropN-∋tv (suc c) (E ∷ Γ) zero    ()       p
dropN-∋tv (suc c) (E ∷ Γ) (suc i) (s≤s le) p =
  dropN-∋tv c Γ i le (∋tv-tail p)

revS-ent-ok : ∀ Γ Θ s k Ξ (S : SCtx) → isConc s Θ ≡ true
            → (revSlots (entᴳ Γ Θ s k ∷ Ξ) ++ S) ∋ok zero
revS-ent-ok Γ Θ s k Ξ S c with isConc s Θ | c
revS-ent-ok Γ Θ s k Ξ S c | true  | _  = hereᵒ
revS-ent-ok Γ Θ s k Ξ S c | false | ()

revS-rvlsᴳ-ok : ∀ k s Γ Θ Ξ₀ (S : SCtx) i → i < k
              → isConc (s + i) Θ ≡ true
              → (revSlots (rvlsᴳ k s Γ Θ ++ Ξ₀) ++ S) ∋ok i
revS-rvlsᴳ-ok zero    s Γ Θ Ξ₀ S i       ()       c
revS-rvlsᴳ-ok (suc k) s Γ Θ Ξ₀ S zero    lt       c =
  revS-ent-ok Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀) S
              (trans (cong (λ n → isConc n Θ) (sym (+-identityʳ s))) c)
revS-rvlsᴳ-ok (suc k) s Γ Θ Ξ₀ S (suc i) (s≤s lt) c =
  revS-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀) S i
    (revS-rvlsᴳ-ok k (suc s) Γ Θ Ξ₀ S i lt
      (trans (cong (λ n → isConc n Θ) (sym (+-suc s i))) c))

-- every slot swapᵇ can reach in the dual's frame is ACCESSIBLE
swap-ok : ∀ {Δ} Γ Θ X → baseS Θ Δ ∋ok X
        → baseS (dualᴳ Γ Θ) (intOf Δ Θ) ∋ok swapᵇ Θ X
swap-ok {Δ} Γ Θ X okp with split (revs Θ) X
swap-ok {Δ} Γ Θ X okp | inj₁ lt =
  ∋ok-≡ (trans (cong (_+ X) (revs-dual Γ Θ))
               (sym (swap-lo (revs Θ) (cmax Θ) X lt)))
        (baseS-ok (dualᴳ Γ Θ) X (inj₂ (isConc-dual Γ Θ X lt))
                  (revE-lo Θ 0 Θ X lt))
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl)
  with baseS-acc Θ i okp
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  ∋ok-≡ (trans (cong (_+ (revs Θ + (i ∸ cmax Θ))) (revs-dual Γ Θ))
          (trans (kept-idx (revs Θ) (cmax Θ) i le)
                 (sym (swap-hi (revs Θ) (cmax Θ) i le))))
        (baseS-ok (dualᴳ Γ Θ) (revs Θ + (i ∸ cmax Θ))
                  (inj₁ (subst (_≤ revs Θ + (i ∸ cmax Θ))
                               (sym (cmax-dual Γ Θ))
                               (m≤m+n (revs Θ) (i ∸ cmax Θ))))
                  (revE-hi Θ 0 Θ
                    (dropN-∋tv (cmax Θ) Δ i le (baseS-∋tv Θ i okp))))
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  ∋ok-≡ (sym (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
        (revS-rvlsᴳ-ok (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ)
                       (slotsᴳ (dualᴳ Γ Θ) 0 (intOf Δ Θ)) i
                       (isConc-< Θ i cc) cc)

sc-dual : ∀ {Δ B} Γ Θ → Scoped (baseS Θ Δ) B
        → Scoped (baseS (dualᴳ Γ Θ) (intOf Δ Θ)) (renameᵗ (swapᵇ Θ) B)
sc-dual Γ Θ sc = sc-rename (λ X okp → swap-ok Γ Θ X okp) sc

------------------------------------------------------------------------
-- Part 4: lengths.  The dual's interior has the same LENGTH as the
-- exterior it rebuilds — the shape half of the context law (the knowledge
-- half is where the Θn residue lives; notes/DECISIONS.md, (R2)).
------------------------------------------------------------------------

len-dropN : ∀ c (Γ : TCtx) → length (dropN c Γ) ≡ length Γ ∸ c
len-dropN zero    Γ       = refl
len-dropN (suc c) []      = refl
len-dropN (suc c) (E ∷ Γ) = len-dropN c Γ

len-++ : ∀ (Ψ₀ Γ : TCtx) → length (Ψ₀ ++ Γ) ≡ length Ψ₀ + length Γ
len-++ []       Γ = refl
len-++ (E ∷ Ψ₀) Γ = cong suc (len-++ Ψ₀ Γ)

len-intOf : ∀ (Γ : TCtx) Θ
          → length (intOf Γ Θ) ≡ revs Θ + (length Γ ∸ cmax Θ)
len-intOf Γ Θ =
  trans (len-++ (revEnts Θ 0 Θ) (dropN (cmax Θ) Γ))
        (cong₂ _+_ (len-revEnts Θ 0 Θ) (len-dropN (cmax Θ) Γ))

len-dual : ∀ (Δ : TCtx) Γ Θ → cmax Θ ≤ length Δ
         → length Δ ≡ length (intOf (intOf Δ Θ) (dualᴳ Γ Θ))
len-dual Δ Γ Θ le =
  sym (trans (len-intOf (intOf Δ Θ) (dualᴳ Γ Θ))
        (trans (cong₂ (λ a b → a + (length (intOf Δ Θ) ∸ b))
                      (revs-dual Γ Θ) (cmax-dual Γ Θ))
          (trans (cong (λ n → cmax Θ + (n ∸ revs Θ)) (len-intOf Δ Θ))
            (trans (cong (cmax Θ +_)
                         (m+n∸m≡n (revs Θ) (length Δ ∸ cmax Θ)))
                   (m+[n∸m]≡n le)))))

-- the deepest conceal is a variable of Δ, so the dropped prefix is no
-- longer than Δ — the side condition len-dual needs
∋tv-len-bound : ∀ {Γ : TCtx} {X} → Γ ∋tv X → suc X ≤ length Γ
∋tv-len-bound here-abst     = s≤s z≤n
∋tv-len-bound here-rvld     = s≤s z≤n
∋tv-len-bound (skip-abst p) = s≤s (∋tv-len-bound p)
∋tv-len-bound (skip-rvld p) = s≤s (∋tv-len-bound p)

bwf-cmax : ∀ {Δ Ψ Θ} Ξ → Bwf Δ Ψ Θ Ξ → cmax Ξ ≤ length Δ
bwf-cmax []            bwf[]             = z≤n
bwf-cmax (rvl A ∷ Ξ)   (bwf↑ wfA b)      = bwf-cmax Ξ b
bwf-cmax (rvl⋆ ∷ Ξ)    (bwf⋆ b)          = bwf-cmax Ξ b
bwf-cmax (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) =
  ⊔-lub (∋tv-len-bound (∋:=→∋tv p)) (bwf-cmax Ξ b)

------------------------------------------------------------------------
-- Part 5: the dual's well-formedness, block by block.  Its REVEAL block
-- asks that every re-introduced rep be well formed over the dual's
-- exterior extended by the deeper dual reveals (the telescope); its
-- CONCEAL block asks that the dual's exterior — Θ's interior — KNOW each
-- reveal variable, and that Θ's external face read back to that knowledge.
-- The second is exactly where the (R2) residue lives (a reveal whose rep
-- names a slot its own boundary blocks gets an `abst` interior entry, so
-- there is no knowledge to meet); it is left as a pointwise obligation for
-- the preservation proof rather than being assumed here.
------------------------------------------------------------------------

bwf-++ : ∀ {Γ Ψ Θ} Ξ₁ Ξ₂ → revs Ξ₂ ≡ 0
       → Bwf Γ Ψ Θ Ξ₁ → Bwf Γ Ψ Θ Ξ₂ → Bwf Γ Ψ Θ (Ξ₁ ++ Ξ₂)
bwf-++ []             Ξ₂ e bwf[]              b₂ = b₂
bwf-++ (rvl A ∷ Ξ₁)   Ξ₂ e (bwf↑ wfA b)       b₂ =
  bwf↑ (subst (λ r → prepAbst r _ ⊢ A) eq wfA) (bwf-++ Ξ₁ Ξ₂ e b b₂)
  where eq : revs Ξ₁ ≡ revs (Ξ₁ ++ Ξ₂)
        eq = sym (trans (revs-++ Ξ₁ Ξ₂)
                        (trans (cong (revs Ξ₁ +_) e)
                               (+-identityʳ (revs Ξ₁))))
bwf-++ (rvl⋆ ∷ Ξ₁)    Ξ₂ e (bwf⋆ b)           b₂ =
  bwf⋆ (bwf-++ Ξ₁ Ξ₂ e b b₂)
bwf-++ (cnc X A ∷ Ξ₁) Ξ₂ e (bwf↓ p rev wfA b) b₂ =
  bwf↓ p rev wfA (bwf-++ Ξ₁ Ξ₂ e b b₂)

bwf-ent : ∀ {Ψ Δ' Θᵈ} Γ Θ s k Ξ
  → (∀ R → entᴳ Γ Θ s k ≡ rvl R → prepAbst (revs Ξ) Ψ ⊢ R)
  → Bwf Ψ Δ' Θᵈ Ξ → Bwf Ψ Δ' Θᵈ (entᴳ Γ Θ s k ∷ Ξ)
bwf-ent Γ Θ s k Ξ h b with isConc s Θ
bwf-ent Γ Θ s k Ξ h b | true  = bwf↑ (h _ refl) b
bwf-ent Γ Θ s k Ξ h b | false with entAt Γ s
bwf-ent Γ Θ s k Ξ h b | false | abst   = bwf⋆ b
bwf-ent Γ Θ s k Ξ h b | false | rvld B = bwf↑ (h _ refl) b

bwf-rvlsᴳ : ∀ {Ψ Δ' Θᵈ} k s Γ Θ Ξ₀
  → (∀ k' s' R → entᴳ Γ Θ s' k' ≡ rvl R
       → prepAbst (k' + revs Ξ₀) Ψ ⊢ R)
  → Bwf Ψ Δ' Θᵈ Ξ₀
  → Bwf Ψ Δ' Θᵈ (rvlsᴳ k s Γ Θ ++ Ξ₀)
bwf-rvlsᴳ zero    s Γ Θ Ξ₀ h b = b
bwf-rvlsᴳ (suc k) s Γ Θ Ξ₀ h b =
  bwf-ent Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀)
    (λ R e → subst (λ r → prepAbst r _ ⊢ R) eq (h k s R e))
    (bwf-rvlsᴳ k (suc s) Γ Θ Ξ₀ h b)
  where eq : k + revs Ξ₀ ≡ revs (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀)
        eq = sym (trans (revs-++ (rvlsᴳ k (suc s) Γ Θ) Ξ₀)
                        (cong (_+ revs Ξ₀) (revs-rvlsᴳ k (suc s) Γ Θ)))

bwf-cncOfRevs : ∀ {Ψ Δ' Θᵈ} j Ξ
  → (∀ k → k < revs Ξ → Σ Ty (λ A₀ →
       (Ψ ∋ (j + k) := A₀) × Reversal Θᵈ (j + k) (ρᵇ Ξ k) A₀))
  → (∀ k → k < revs Ξ → Δ' ⊢ ρᵇ Ξ k)
  → Bwf Ψ Δ' Θᵈ (cncOfRevs j Ξ)
bwf-cncOfRevs j []            hk hw = bwf[]
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl A ∷ Ξ) hk hw with hk 0 (s≤s z≤n)
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl A ∷ Ξ) hk hw | A₀ , p , rev =
  bwf↓ (subst (λ n → Ψ ∋ n := A₀) (+-identityʳ j) p)
       (subst (λ n → Reversal Θᵈ n (substᵗ (ρᵇ Ξ) A) A₀)
              (+-identityʳ j) rev)
       (hw 0 (s≤s z≤n))
       (bwf-cncOfRevs (suc j) Ξ
         (λ k lt → shiftΣ k lt (hk (suc k) (s≤s lt)))
         (λ k lt → hw (suc k) (s≤s lt)))
  where
    shiftΣ : ∀ k → k < revs Ξ
           → Σ Ty (λ A₀' → (Ψ ∋ (j + suc k) := A₀')
                × Reversal Θᵈ (j + suc k) (ρᵇ Ξ k) A₀')
           → Σ Ty (λ A₀' → (Ψ ∋ (suc j + k) := A₀')
                × Reversal Θᵈ (suc j + k) (ρᵇ Ξ k) A₀')
    shiftΣ k lt (A₀' , q , rv) =
      A₀' , subst (λ n → Ψ ∋ n := A₀') (+-suc j k) q
          , subst (λ n → Reversal Θᵈ n (ρᵇ Ξ k) A₀') (+-suc j k) rv
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl⋆ ∷ Ξ) hk hw with hk 0 (s≤s z≤n)
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl⋆ ∷ Ξ) hk hw | A₀ , p , rev =
  bwf↓ (subst (λ n → Ψ ∋ n := A₀) (+-identityʳ j) p)
       (subst (λ n → Reversal Θᵈ n `ℕ A₀) (+-identityʳ j) rev)
       (hw 0 (s≤s z≤n))
       (bwf-cncOfRevs (suc j) Ξ
         (λ k lt → shiftΣ k lt (hk (suc k) (s≤s lt)))
         (λ k lt → hw (suc k) (s≤s lt)))
  where
    shiftΣ : ∀ k → k < revs Ξ
           → Σ Ty (λ A₀' → (Ψ ∋ (j + suc k) := A₀')
                × Reversal Θᵈ (j + suc k) (ρᵇ Ξ k) A₀')
           → Σ Ty (λ A₀' → (Ψ ∋ (suc j + k) := A₀')
                × Reversal Θᵈ (suc j + k) (ρᵇ Ξ k) A₀')
    shiftΣ k lt (A₀' , q , rv) =
      A₀' , subst (λ n → Ψ ∋ n := A₀') (+-suc j k) q
          , subst (λ n → Reversal Θᵈ n (ρᵇ Ξ k) A₀') (+-suc j k) rv
bwf-cncOfRevs j (cnc X A ∷ Ξ) hk hw = bwf-cncOfRevs j Ξ hk hw

------------------------------------------------------------------------
-- KNOWLEDGE INTERIORS TRANSPORT.  The interior's reveal entries carry the
-- interior reading ⟦A⟧ of each reveal's rep, so ⊢renameᵀ's (env) case must
-- show that those entries move with the renaming.  The chain is:
--   slotAt-ren  → bfree-ren      (the blocked-freeness guard is stable)
--   γcnc-comm   → rawRead-ren    (the reading commutes, at accessible slots)
--   dfree-ren   → dnT-ren        (the telescope guard is stable, and the
--                                 down-shift commutes where it holds)
-- and hence ⟦⟧-ren, revEnts-ren, ∋:=-int.
------------------------------------------------------------------------

slot-dich : ∀ (s : Slot) → (s ≡ ok) ⊎ (s ≡ blk)
slot-dich ok  = inj₁ refl
slot-dich blk = inj₂ refl

isOk-ok : ∀ (s : Slot) → isOk s ≡ true → s ≡ ok
isOk-ok ok  e = refl
isOk-ok blk ()

ok-isOk : ∀ (s : Slot) → s ≡ ok → isOk s ≡ true
ok-isOk ok  e = refl
ok-isOk blk ()

mono-lt-inv : ∀ {ρ} → Mono ρ → ∀ {a b} → ρ a < ρ b → a < b
mono-lt-inv {ρ} mono {a} {b} lt with a <? b
mono-lt-inv {ρ} mono {a} {b} lt | yes p  = p
mono-lt-inv {ρ} mono {a} {b} lt | no ¬p  =
  ⊥-elim (<-irrefl refl
           (≤-trans lt (Mono→≤ mono (≤-pred (≰⇒> ¬p)))))

acc-ren-inv : ∀ {ρ} → Mono ρ → ∀ Θ i
  → (cmax (renᴮ ρ (intRen ρ Θ) Θ) ≤ ρ i)
    ⊎ (isConc (ρ i) (renᴮ ρ (intRen ρ Θ) Θ) ≡ true)
  → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
acc-ren-inv {ρ} mono Θ i (inj₂ c) =
  inj₂ (isConc-ren-inv mono (intRen ρ Θ) Θ i c)
acc-ren-inv {ρ} mono Θ i (inj₁ le) with cmax-ren mono (intRen ρ Θ) Θ
acc-ren-inv {ρ} mono Θ i (inj₁ le) | cm-0 e e' =
  inj₁ (subst (_≤ i) (sym e) z≤n)
acc-ren-inv {ρ} mono Θ i (inj₁ le) | cm-s X e e' =
  inj₁ (subst (_≤ i) (sym e) (mono-lt-inv mono (subst (_≤ ρ i) e' le)))

slotAt-ren : ∀ {ρ} → Mono ρ → ∀ Θ i
           → slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i) ≡ slotAt Θ i
slotAt-ren {ρ} mono Θ i with slot-dich (slotAt Θ i)
slotAt-ren {ρ} mono Θ i | inj₁ e =
  trans (acc-slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)
                    (acc-ren mono Θ i (acc-of Θ i e)))
        (sym e)
slotAt-ren {ρ} mono Θ i | inj₂ e
  with slot-dich (slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i))
slotAt-ren {ρ} mono Θ i | inj₂ e | inj₂ b = trans b (sym e)
slotAt-ren {ρ} mono Θ i | inj₂ e | inj₁ o =
  ⊥-elim (ok≢blk
    (trans (sym (acc-slotAt Θ i
                  (acc-ren-inv mono Θ i
                    (acc-of (renᴮ ρ (intRen ρ Θ) Θ) (ρ i) o))))
           e))

bfree-ren : ∀ {ρ} → Mono ρ → ∀ Θ d A
  → bfree (renᴮ ρ (intRen ρ Θ) Θ) d (renameᵗ (liftⁿ d ρ) A)
    ≡ bfree Θ d A
bfree-ren {ρ} mono Θ d (` X) with split d X
bfree-ren {ρ} mono Θ d (` X) | inj₁ lt
  rewrite liftⁿ-lo d ρ X lt | ⌊⌋-of (X <? d) lt = refl
bfree-ren {ρ} mono Θ d (` .(d + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi d ρ i =
  cong₂ _∨_
    (trans (⌊⌋-false ((d + ρ i) <? d) (m+n≮m d (ρ i)))
           (sym (⌊⌋-false ((d + i) <? d) (m+n≮m d i))))
    (trans (cong (λ n → isOk (slotAt (renᴮ ρ (intRen ρ Θ) Θ) n))
                 (m+n∸m≡n d (ρ i)))
      (trans (cong isOk (slotAt-ren mono Θ i))
             (cong (λ n → isOk (slotAt Θ n)) (sym (m+n∸m≡n d i)))))
bfree-ren mono Θ d `ℕ      = refl
bfree-ren mono Θ d `𝔹      = refl
bfree-ren mono Θ d (A ⇒ B) =
  cong₂ _∧_ (bfree-ren mono Θ d A) (bfree-ren mono Θ d B)
bfree-ren mono Θ d (`∀ A)  = bfree-ren mono Θ (suc d) A

∧-true : ∀ (b₁ b₂ : Bool) → (b₁ ∧ b₂) ≡ true
       → (b₁ ≡ true) × (b₂ ≡ true)
∧-true true  true  e  = refl , refl
∧-true true  false ()
∧-true false b₂    ()

⌊⌋-iff : ∀ {P Q : Set} (dp : Dec P) (dq : Dec Q)
       → (P → Q) → (Q → P) → ⌊ dp ⌋ ≡ ⌊ dq ⌋
⌊⌋-iff (yes p) (yes q) f g = refl
⌊⌋-iff (yes p) (no ¬q) f g = ⊥-elim (¬q (f p))
⌊⌋-iff (no ¬p) (yes q) f g = ⊥-elim (¬p (g q))
⌊⌋-iff (no ¬p) (no ¬q) f g = refl

rdSub-lo : ∀ Θ j d k → k < d → rdSub Θ j d k ≡ ` (suc j + k)
rdSub-lo Θ j d k lt with k <? d
rdSub-lo Θ j d k lt | yes _  = refl
rdSub-lo Θ j d k lt | no ¬lt = ⊥-elim (¬lt lt)

rdSub-hi : ∀ Θ j d i → rdSub Θ j d (d + i) ≡ γcnc (revs Θ) (cmax Θ) Θ i
rdSub-hi Θ j d i with (d + i) <? d
rdSub-hi Θ j d i | yes lt = ⊥-elim (m+n≮m d i lt)
rdSub-hi Θ j d i | no  _  =
  cong (γcnc (revs Θ) (cmax Θ) Θ) (m+n∸m≡n d i)

exts-step : ∀ (σ' σ : Substᵗ) g m n → σ' m ≡ renameᵗ g (σ n)
          → extsᵗ σ' (suc m) ≡ renameᵗ (extᵗ g) (extsᵗ σ (suc n))
exts-step σ' σ g m n e =
  trans (cong (renameᵗ suc) e)
    (trans (rename-rename-commute g suc (σ n))
           (sym (rename-rename-commute suc (extᵗ g) (σ n))))

-- substitution congruence up to a renaming, restricted by bfree: the two
-- substitutions need only agree at the slots the type may name
bf-cong : ∀ Θ d (σ' σ : Substᵗ) (f g : ℕ → ℕ) A
  → bfree Θ d A ≡ true
  → (∀ X → X < d → σ' (liftⁿ d f X) ≡ renameᵗ g (σ X))
  → (∀ i → slotAt Θ i ≡ ok
         → σ' (liftⁿ d f (d + i)) ≡ renameᵗ g (σ (d + i)))
  → substᵗ σ' (renameᵗ (liftⁿ d f) A) ≡ renameᵗ g (substᵗ σ A)
bf-cong Θ d σ' σ f g (` X) bf h1 h2 with split d X
bf-cong Θ d σ' σ f g (` X) bf h1 h2 | inj₁ lt = h1 X lt
bf-cong Θ d σ' σ f g (` .(d + i)) bf h1 h2 | inj₂ (i , refl) =
  h2 i (isOk-ok (slotAt Θ i)
         (trans (cong (λ n → isOk (slotAt Θ n)) (sym (m+n∸m≡n d i)))
                (trans (sym (cong (λ b → b ∨ isOk (slotAt Θ ((d + i) ∸ d)))
                                  (⌊⌋-false ((d + i) <? d) (m+n≮m d i))))
                       bf)))
bf-cong Θ d σ' σ f g `ℕ bf h1 h2 = refl
bf-cong Θ d σ' σ f g `𝔹 bf h1 h2 = refl
bf-cong Θ d σ' σ f g (A ⇒ B) bf h1 h2 =
  cong₂ _⇒_ (bf-cong Θ d σ' σ f g A (fst (∧-true _ _ bf)) h1 h2)
            (bf-cong Θ d σ' σ f g B (snd (∧-true _ _ bf)) h1 h2)
  where fst : ∀ {P Q : Set} → P × Q → P
        fst (p , q) = p
        snd : ∀ {P Q : Set} → P × Q → Q
        snd (p , q) = q
bf-cong Θ d σ' σ f g (`∀ A) bf h1 h2 =
  cong `∀ (bf-cong Θ (suc d) (extsᵗ σ') (extsᵗ σ) f (extᵗ g) A bf h1' h2')
  where
    h1' : ∀ X → X < suc d
        → extsᵗ σ' (liftⁿ (suc d) f X) ≡ renameᵗ (extᵗ g) (extsᵗ σ X)
    h1' zero    lt       = refl
    h1' (suc X) (s≤s lt) = exts-step σ' σ g (liftⁿ d f X) X (h1 X lt)
    h2' : ∀ i → slotAt Θ i ≡ ok
        → extsᵗ σ' (liftⁿ (suc d) f (suc d + i))
          ≡ renameᵗ (extᵗ g) (extsᵗ σ (suc d + i))
    h2' i okp = exts-step σ' σ g (liftⁿ d f (d + i)) (d + i) (h2 i okp)

rawRead-ren : ∀ {ρ} → Mono ρ → ∀ Θ j d A → suc j + d ≡ revs Θ
  → bfree Θ d A ≡ true
  → rawRead (renᴮ ρ (intRen ρ Θ) Θ) j d (renameᵗ (liftⁿ d ρ) A)
    ≡ renameᵗ (intRen ρ Θ) (rawRead Θ j d A)
rawRead-ren {ρ} mono Θ j d A hd bf =
  bf-cong Θ d (rdSub Θ' j d) (rdSub Θ j d) ρ (intRen ρ Θ) A bf h1 h2
  where
    Θ' = renᴮ ρ (intRen ρ Θ) Θ
    h1 : ∀ X → X < d → rdSub Θ' j d (liftⁿ d ρ X)
                       ≡ renameᵗ (intRen ρ Θ) (rdSub Θ j d X)
    h1 X lt =
      trans (cong (rdSub Θ' j d) (liftⁿ-lo d ρ X lt))
        (trans (rdSub-lo Θ' j d X lt)
          (trans (cong `_ (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ)
                                         (suc j + X) sjX)))
                 (cong (renameᵗ (intRen ρ Θ)) (sym (rdSub-lo Θ j d X lt)))))
      where sjX : suc j + X < revs Θ
            sjX = subst (suc j + X <_) hd (+-monoʳ-< (suc j) lt)
    h2 : ∀ i → slotAt Θ i ≡ ok
       → rdSub Θ' j d (liftⁿ d ρ (d + i))
         ≡ renameᵗ (intRen ρ Θ) (rdSub Θ j d (d + i))
    h2 i okp =
      trans (cong (rdSub Θ' j d) (liftⁿ-hi d ρ i))
        (trans (rdSub-hi Θ' j d (ρ i))
          (trans (cong (λ r → γcnc r (cmax Θ') Θ' (ρ i))
                       (revs-ren ρ (intRen ρ Θ) Θ))
            (trans (γcnc-comm mono (revs Θ) (cmax Θ) (cmax Θ') Θ i
                              (deep-hyp mono Θ) (acc-of Θ i okp))
                   (cong (renameᵗ (intRen ρ Θ)) (sym (rdSub-hi Θ j d i))))))

dfree-ren : ∀ τ → Mono τ → ∀ j → τ j ≡ j → ∀ b T
  → dfree b (suc j) (renameᵗ (liftⁿ b τ) T) ≡ dfree b (suc j) T
dfree-ren τ mono j hj b (` X) with split b X
dfree-ren τ mono j hj b (` X) | inj₁ lt
  rewrite liftⁿ-lo b τ X lt = refl
dfree-ren τ mono j hj b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b τ i =
  cong₂ _∨_
    (trans (⌊⌋-false ((b + τ i) <? b) (m+n≮m b (τ i)))
           (sym (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
    (⌊⌋-iff ((b + suc j) ≤? (b + τ i)) ((b + suc j) ≤? (b + i)) fwd bwd)
  where
    fwd : b + suc j ≤ b + τ i → b + suc j ≤ b + i
    fwd le = +-monoʳ-≤ b
               (mono-lt-inv mono
                 (subst (_< τ i) (sym hj) (+-cancelˡ-≤ b _ _ le)))
    bwd : b + suc j ≤ b + i → b + suc j ≤ b + τ i
    bwd le = +-monoʳ-≤ b
               (subst (_< τ i) hj (mono (+-cancelˡ-≤ b _ _ le)))
dfree-ren τ mono j hj b `ℕ      = refl
dfree-ren τ mono j hj b `𝔹      = refl
dfree-ren τ mono j hj b (T ⇒ U) =
  cong₂ _∧_ (dfree-ren τ mono j hj b T) (dfree-ren τ mono j hj b U)
dfree-ren τ mono j hj b (`∀ T)  = dfree-ren τ mono j hj (suc b) T

dnT-ren : ∀ τ j → τ j ≡ j → ∀ b T → dfree b (suc j) T ≡ true
  → renameᵗ (liftⁿ b (_∸ suc j)) (renameᵗ (liftⁿ b τ) T)
    ≡ renameᵗ (liftⁿ b (restrictRen j τ)) (renameᵗ (liftⁿ b (_∸ suc j)) T)
dnT-ren τ j hj b (` X) df with split b X
dnT-ren τ j hj b (` X) df | inj₁ lt
  rewrite liftⁿ-lo b τ X lt | liftⁿ-lo b (_∸ suc j) X lt
        | liftⁿ-lo b (restrictRen j τ) X lt = refl
dnT-ren τ j hj b (` .(b + i)) df | inj₂ (i , refl)
  rewrite liftⁿ-hi b τ i | liftⁿ-hi b (_∸ suc j) (τ i)
        | liftⁿ-hi b (_∸ suc j) i
        | liftⁿ-hi b (restrictRen j τ) (i ∸ suc j) =
  cong (λ n → ` (b + n)) key
  where
    sj≤i : suc j ≤ i
    sj≤i = +-cancelˡ-≤ b _ _
             (⌊⌋-true ((b + suc j) ≤? (b + i))
               (trans (sym (cong (λ c → c ∨ ⌊ (b + suc j) ≤? (b + i) ⌋)
                                 (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
                      df))
    key : τ i ∸ suc j ≡ restrictRen j τ (i ∸ suc j)
    key = cong₂ _∸_ (cong τ (sym (m+[n∸m]≡n sj≤i))) (cong suc (sym hj))
dnT-ren τ j hj b `ℕ      df = refl
dnT-ren τ j hj b `𝔹      df = refl
dnT-ren τ j hj b (T ⇒ U) df =
  cong₂ _⇒_ (dnT-ren τ j hj b T (fst (∧-true _ _ df)))
            (dnT-ren τ j hj b U (snd (∧-true _ _ df)))
  where fst : ∀ {P Q : Set} → P × Q → P
        fst (p , q) = p
        snd : ∀ {P Q : Set} → P × Q → Q
        snd (p , q) = q
dnT-ren τ j hj b (`∀ T)  df = cong `∀ (dnT-ren τ j hj (suc b) T df)

------------------------------------------------------------------------
-- The interior ENTRIES transport, and hence the interior's knowledge.
------------------------------------------------------------------------

entRen : (ℕ → ℕ) → TyEntry → TyEntry
entRen f abst     = abst
entRen f (rvld A) = rvld (renameᵗ f A)

ent-if : ∀ (b b' : Bool) (T T' : Ty) (f : ℕ → ℕ)
       → b' ≡ b → (b ≡ true → T' ≡ renameᵗ f T)
       → (if b' then rvld T' else abst)
         ≡ entRen f (if b then rvld T else abst)
ent-if true  b' T T' f e₁ e₂ rewrite e₁ = cong rvld (e₂ refl)
ent-if false b' T T' f e₁ e₂ rewrite e₁ = refl

⟦⟧-ren : ∀ {ρ} → Mono ρ → ∀ Θ j d A → suc j + d ≡ revs Θ
  → ⟦ renᴮ ρ (intRen ρ Θ) Θ ⟧ᵉ j d (renameᵗ (liftⁿ d ρ) A)
    ≡ entRen (restrictRen j (intRen ρ Θ)) (⟦ Θ ⟧ᵉ j d A)
⟦⟧-ren {ρ} mono Θ j d A hd with bfree Θ d A in eb
⟦⟧-ren {ρ} mono Θ j d A hd | false
  rewrite trans (bfree-ren mono Θ d A) eb = refl
⟦⟧-ren {ρ} mono Θ j d A hd | true
  rewrite trans (bfree-ren mono Θ d A) eb
        | rawRead-ren mono Θ j d A hd eb =
  ent-if (dfree 0 (suc j) (rawRead Θ j d A))
         (dfree 0 (suc j) (renameᵗ (intRen ρ Θ) (rawRead Θ j d A)))
         (dnT (suc j) (rawRead Θ j d A))
         (dnT (suc j) (renameᵗ (intRen ρ Θ) (rawRead Θ j d A)))
         (restrictRen j (intRen ρ Θ))
         (dfree-ren (intRen ρ Θ) (Mono-intRen Θ mono) j τj 0
                    (rawRead Θ j d A))
         (λ df → dnT-ren (intRen ρ Θ) j τj 0 (rawRead Θ j d A) df)
  where τj : intRen ρ Θ j ≡ j
        τj = liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) j
                      (subst (j <_) hd (m≤m+n (suc j) d))

mapEnts : (ℕ → TyEntry → TyEntry) → ℕ → TCtx → TCtx
mapEnts f j []      = []
mapEnts f j (E ∷ Ψ) = f j E ∷ mapEnts f (suc j) Ψ

revEnts-ren : ∀ {ρ} → Mono ρ → ∀ Θ j Ξ → j + revs Ξ ≡ revs Θ
  → revEnts (renᴮ ρ (intRen ρ Θ) Θ) j (renᴮ ρ (intRen ρ Θ) Ξ)
    ≡ mapEnts (λ n → entRen (restrictRen n (intRen ρ Θ))) j
              (revEnts Θ j Ξ)
revEnts-ren mono Θ j []            hj = refl
revEnts-ren {ρ} mono Θ j (rvl A ∷ Ξ) hj =
  cong₂ _∷_ eq-head (revEnts-ren mono Θ (suc j) Ξ hd)
  where
    hd : suc j + revs Ξ ≡ revs Θ
    hd = trans (sym (+-suc j (revs Ξ))) hj
    eq-head : ⟦ renᴮ ρ (intRen ρ Θ) Θ ⟧ᵉ j
                (revs (renᴮ ρ (intRen ρ Θ) Ξ))
                (renameᵗ (liftⁿ (revs Ξ) ρ) A)
              ≡ entRen (restrictRen j (intRen ρ Θ)) (⟦ Θ ⟧ᵉ j (revs Ξ) A)
    eq-head rewrite revs-ren ρ (intRen ρ Θ) Ξ =
      ⟦⟧-ren mono Θ j (revs Ξ) A hd
revEnts-ren {ρ} mono Θ j (rvl⋆ ∷ Ξ) hj =
  cong (abst ∷_) (revEnts-ren mono Θ (suc j) Ξ hd)
  where
    hd : suc j + revs Ξ ≡ revs Θ
    hd = trans (sym (+-suc j (revs Ξ))) hj
revEnts-ren mono Θ j (cnc X A ∷ Ξ) hj = revEnts-ren mono Θ j Ξ hj

∋:=-cong : ∀ {Δ : TCtx} {X : ℕ} {A B : Ty} → A ≡ B → Δ ∋ X := A → Δ ∋ X := B
∋:=-cong refl p = p

mapEnts-∋:= : ∀ (g : ℕ → ℕ → ℕ) j (Ψ₀ : TCtx) {Γ Γ' : TCtx} {Y B}
  → Y < length Ψ₀ → (Ψ₀ ++ Γ) ∋ Y := B
  → (mapEnts (λ n → entRen (g n)) j Ψ₀ ++ Γ') ∋ Y := renameᵗ (g (j + Y)) B
mapEnts-∋:= g j []              () p
mapEnts-∋:= g j (rvld A ∷ Ψ₀)   lt here =
  ∋:=-cong (cong (λ n → renameᵗ (g n) A) (sym (+-identityʳ j))) here
mapEnts-∋:= g j (abst ∷ Ψ₀) {Y = suc Y} {B} (s≤s lt) (skip-abst p) =
  ∋:=-cong (cong (λ n → renameᵗ (g n) B) (sym (+-suc j Y)))
           (skip-abst (mapEnts-∋:= g (suc j) Ψ₀ lt p))
mapEnts-∋:= g j (rvld A ∷ Ψ₀) {Y = suc Y} {B} (s≤s lt) (skip-rvld p) =
  ∋:=-cong (cong (λ n → renameᵗ (g n) B) (sym (+-suc j Y)))
           (skip-rvld (mapEnts-∋:= g (suc j) Ψ₀ lt p))

------------------------------------------------------------------------
-- The exterior part: a knowledge entry deeper than the deepest conceal is
-- an entry of Δ itself, and the induced renaming on the interior's tail is
-- the one the exterior hypothesis provides.
------------------------------------------------------------------------

dropN-∋:= : ∀ c (Δ : TCtx) {Z B} → dropN c Δ ∋ Z := B → Δ ∋ (c + Z) := B
dropN-∋:= zero    Δ            p = p
dropN-∋:= (suc c) []           ()
dropN-∋:= (suc c) (abst ∷ Δ)   p = skip-abst (dropN-∋:= c Δ p)
dropN-∋:= (suc c) (rvld A ∷ Δ) p = skip-rvld (dropN-∋:= c Δ p)

dropN-∋:=⁻ : ∀ c (Δ : TCtx) {Z B} → Δ ∋ (c + Z) := B → dropN c Δ ∋ Z := B
dropN-∋:=⁻ zero    Δ            p             = p
dropN-∋:=⁻ (suc c) []           ()
dropN-∋:=⁻ (suc c) (abst ∷ Δ)   (skip-abst p) = dropN-∋:=⁻ c Δ p
dropN-∋:=⁻ (suc c) (rvld A ∷ Δ) (skip-rvld p) = dropN-∋:=⁻ c Δ p

ent-skip:= : ∀ (E : TyEntry) {Δ X A} → Δ ∋ X := A → (E ∷ Δ) ∋ suc X := A
ent-skip:= abst     p = skip-abst p
ent-skip:= (rvld B) p = skip-rvld p

ent-tail:= : ∀ (E : TyEntry) {Δ X A} → (E ∷ Δ) ∋ suc X := A → Δ ∋ X := A
ent-tail:= abst     (skip-abst p) = p
ent-tail:= (rvld B) (skip-rvld p) = p

revE-hi:= : ∀ Θ j Ξ {Γ : TCtx} {Z B} → Γ ∋ Z := B
          → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) := B
revE-hi:= Θ j []            p = p
revE-hi:= Θ j (rvl A ∷ Ξ)   p =
  ent-skip:= (⟦ Θ ⟧ᵉ j (revs Ξ) A) (revE-hi:= Θ (suc j) Ξ p)
revE-hi:= Θ j (rvl⋆ ∷ Ξ)    p = skip-abst (revE-hi:= Θ (suc j) Ξ p)
revE-hi:= Θ j (cnc X A ∷ Ξ) p = revE-hi:= Θ j Ξ p

revE-hi:=⁻ : ∀ Θ j Ξ {Γ : TCtx} {Z B}
           → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) := B → Γ ∋ Z := B
revE-hi:=⁻ Θ j []            p = p
revE-hi:=⁻ Θ j (rvl A ∷ Ξ)   p =
  revE-hi:=⁻ Θ (suc j) Ξ (ent-tail:= (⟦ Θ ⟧ᵉ j (revs Ξ) A) p)
revE-hi:=⁻ Θ j (rvl⋆ ∷ Ξ)    p =
  revE-hi:=⁻ Θ (suc j) Ξ (ent-tail:= abst p)
revE-hi:=⁻ Θ j (cnc X A ∷ Ξ) p = revE-hi:=⁻ Θ j Ξ p

∸∸-lemma : ∀ a b n → n ≤ b → (a ∸ n) ∸ suc (b ∸ n) ≡ a ∸ suc b
∸∸-lemma a b n le =
  trans (cong (λ m → (a ∸ n) ∸ m) (sym (+-∸-assoc 1 le)))
    (trans (∸-+-assoc a n (suc b ∸ n))
           (cong (a ∸_) (m+[n∸m]≡n (≤-trans le (n≤1+n b)))))

restrict-deep : ∀ {ρ} → Mono ρ → ∀ c Z k
  → restrictRen Z (deepRen c ρ) k ≡ restrictRen (c + Z) ρ k
restrict-deep mono zero    Z k = refl
restrict-deep {ρ} mono (suc X) Z k =
  trans (cong (λ u → (u ∸ suc (ρ X))
                     ∸ suc (ρ (suc X + Z) ∸ suc (ρ X)))
              (cong ρ idx))
        (∸∸-lemma (ρ (suc (suc X + Z) + k)) (ρ (suc X + Z)) (suc (ρ X)) nb)
  where
    idx : suc X + (suc Z + k) ≡ suc (suc X + Z) + k
    idx = cong suc (trans (+-suc X (Z + k))
                          (cong suc (sym (+-assoc X Z k))))
    nb : suc (ρ X) ≤ ρ (suc X + Z)
    nb = mono (m≤m+n (suc X) Z)

+∸+ : ∀ r x y → (r + x) ∸ (r + y) ≡ x ∸ y
+∸+ r x y =
  trans (sym (∸-+-assoc (r + x) r y)) (cong (_∸ y) (m+n∸m≡n r x))

restrict-int : ∀ {ρ} → Mono ρ → ∀ Θ Z k
  → restrictRen (revs Θ + Z) (intRen ρ Θ) k
    ≡ restrictRen (cmax Θ + Z) ρ k
restrict-int {ρ} mono Θ Z k =
  trans (cong₂ _∸_ (trans (cong (intRen ρ Θ) idx)
                          (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ)
                                    (suc Z + k)))
                   (trans (cong suc (liftⁿ-hi (revs Θ)
                                       (deepRen (cmax Θ) ρ) Z))
                          (sym (+-suc (revs Θ) (deepRen (cmax Θ) ρ Z)))))
    (trans (+∸+ (revs Θ) (deepRen (cmax Θ) ρ (suc Z + k))
                (suc (deepRen (cmax Θ) ρ Z)))
           (restrict-deep mono (cmax Θ) Z k))
  where
    idx : suc (revs Θ + Z) + k ≡ revs Θ + (suc Z + k)
    idx = trans (cong suc (+-assoc (revs Θ) Z k))
                (sym (+-suc (revs Θ) (Z + k)))

∋:=-int : ∀ {ρ Δ Δ'} → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → ∀ Θ {Y B}
  → intOf Δ Θ ∋ Y := B
  → intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋ intRen ρ Θ Y
      := renameᵗ (restrictRen Y (intRen ρ Θ)) B
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {Y} {B} p with split (revs Θ) Y
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {Y} {B} p | inj₁ lt =
  subst (λ Ψ₀ → (Ψ₀ ++ dropN (cmax Θ') Δ')
                ∋ intRen ρ Θ Y := renameᵗ (restrictRen Y (intRen ρ Θ)) B)
        (sym (revEnts-ren mono Θ 0 Θ refl))
        (subst (λ n → (mapEnts (λ m → entRen (restrictRen m (intRen ρ Θ)))
                               0 (revEnts Θ 0 Θ) ++ dropN (cmax Θ') Δ')
                      ∋ n := renameᵗ (restrictRen Y (intRen ρ Θ)) B)
               (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
               (mapEnts-∋:= (λ n → restrictRen n (intRen ρ Θ)) 0
                            (revEnts Θ 0 Θ)
                            (subst (Y <_) (sym (len-revEnts Θ 0 Θ)) lt) p))
  where Θ' = renᴮ ρ (intRen ρ Θ) Θ
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {.(revs Θ + Z)} {B} p | inj₂ (Z , refl) =
  subst₂ (λ n C → intOf Δ' Θ' ∋ n := C) idx rep
    (revE-hi:= Θ' 0 Θ'
      (dropN-∋:=⁻ (cmax Θ') Δ'
        (subst (λ n → Δ' ∋ n := renameᵗ (restrictRen (cmax Θ + Z) ρ) B)
               (sym key)
               (hk (dropN-∋:= (cmax Θ) Δ (revE-hi:=⁻ Θ 0 Θ p))))))
  where
    Θ' = renᴮ ρ (intRen ρ Θ) Θ
    idx : revs Θ' + deepRen (cmax Θ) ρ Z ≡ intRen ρ Θ (revs Θ + Z)
    idx = trans (cong (_+ deepRen (cmax Θ) ρ Z)
                      (revs-ren ρ (intRen ρ Θ) Θ))
                (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z))
    rep : renameᵗ (restrictRen (cmax Θ + Z) ρ) B
        ≡ renameᵗ (restrictRen (revs Θ + Z) (intRen ρ Θ)) B
    rep = rename-cong (λ k → sym (restrict-int mono Θ Z k)) B
    key : cmax Θ' + deepRen (cmax Θ) ρ Z ≡ ρ (cmax Θ + Z)
    key with cmax-ren mono (intRen ρ Θ) Θ
    key | cm-0 e e′ rewrite e | e′ = refl
    key | cm-s W e e′ rewrite e | e′ =
      m+[n∸m]≡n (mono {W} {suc W + Z} (m≤m+n (suc W) Z))

------------------------------------------------------------------------
-- Type-variable renaming preserves typing.
--
-- ρ must be MONOTONE, not merely lookup-preserving: boundary renaming
-- depends on index order through cmax / restrictRen (a non-monotone ρ that
-- permutes indices could shrink a conceal's interior and strand a
-- variable).  And, since the reversal premise reads the exterior's
-- KNOWLEDGE, ρ must also transport ∋:= — the third hypothesis, which the
-- interior-form rework identified: it holds at `suc` because
-- restrictRen X suc is pointwise the identity, and it extends under a Λ
-- because restrictRen (suc X) (extᵗ ρ) is pointwise restrictRen X ρ.
------------------------------------------------------------------------

hk-ext : ∀ {ρ Δ Δ'}
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → ∀ {X A₀} → (abst ∷ Δ) ∋ X := A₀
  → (abst ∷ Δ') ∋ extᵗ ρ X := renameᵗ (restrictRen X (extᵗ ρ)) A₀
hk-ext hk (skip-abst p) = skip-abst (hk p)

⊢renameᵀ : ∀ {ρ Δ Δ' Γₜ M A}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
⊢renameᵀ h mono hk (⊢` p)      = ⊢` (∋-map p)
⊢renameᵀ h mono hk ⊢$          = ⊢$
⊢renameᵀ h mono hk (⊢ƛ wfA ⊢N) =
  ⊢ƛ (wf-ren h wfA) (⊢renameᵀ h mono hk ⊢N)
⊢renameᵀ h mono hk (⊢· ⊢L ⊢M)  =
  ⊢· (⊢renameᵀ h mono hk ⊢L) (⊢renameᵀ h mono hk ⊢M)
⊢renameᵀ h mono hk (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Γ' → _ ∣ Γ' ⊢ _ ⦂ _) (⤊-ren Γₜ)
            (⊢renameᵀ (ext-h h) (Mono-extᵗ mono) (hk-ext hk) ⊢N))
⊢renameᵀ {ρ} h mono hk (⊢·[] {L = L} {B = B} {A = A} ⊢L wfA) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ ρ L
                     ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ] ⦂ T)
        (sym (rename-[]ᵗ-commute ρ B A))
    (⊢·[] (⊢renameᵀ h mono hk ⊢L) (wf-ren h wfA))
⊢renameᵀ {ρ} h mono hk (env {Θ = Θ} {B₀ = B₀} {M = M} bwf sc ⊢M) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ (intRen ρ Θ) M
                       ⟪ renᴮ ρ (intRen ρ Θ) Θ
                       , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫ ⦂ T)
        (C-ext ρ (intRen ρ Θ) Θ B₀)
    (env (bwf-ren mono h hk (h-int h mono Θ) bwf)
         (sc-ren h mono Θ sc)
         (subst (λ T → _ ∣ [] ⊢ renameᵀ (intRen ρ Θ) M ⦂ T)
                (sym (C-int mono Θ sc))
                (⊢renameᵀ (h-int h mono Θ) (Mono-intRen Θ mono)
                          (∋:=-int mono hk Θ) ⊢M)))

-- the hypothesis really is met by the weakening ⇑ᵀ uses
Mono-suc : Mono suc
Mono-suc lt = s≤s lt

hk-suc : ∀ {Δ : TCtx} {E X A₀} → Δ ∋ X := A₀
       → (E ∷ Δ) ∋ suc X := renameᵗ (restrictRen X suc) A₀
hk-suc {E = E} {X} {A₀} p =
  ent-skip:= E (∋:=-cong (sym (trans (rename-cong (m+n∸m≡n X) A₀)
                                     (rename-id A₀))) p)
  where
    rename-id : ∀ (T : Ty) → renameᵗ (λ i → i) T ≡ T
    rename-id (` X') = refl
    rename-id `ℕ     = refl
    rename-id `𝔹     = refl
    rename-id (T ⇒ U) = cong₂ _⇒_ (rename-id T) (rename-id U)
    rename-id (`∀ T)  =
      cong `∀ (trans (rename-cong ext-id T) (rename-id T))
      where ext-id : ∀ i → extᵗ (λ n → n) i ≡ i
            ext-id zero    = refl
            ext-id (suc i) = refl
------------------------------------------------------------------------
-- The interior of the SHIFTED boundary.  Every reveal of Θ keeps its rep
-- and moves one slot down, and its interior reading moves with it: the
-- conceal reps shift by suc (γcnc-shift) and the entry's own down-shift
-- absorbs it, so the entries are UNCHANGED.  No accessibility condition is
-- needed here — unlike renaming, the shift agrees at every slot.
------------------------------------------------------------------------

bfree-shift : ∀ A Θ d A₁
  → bfree (rvl A ∷ shiftReps Θ) d A₁ ≡ bfree Θ d A₁
bfree-shift A Θ d (` X)   =
  cong (λ s → ⌊ X <? d ⌋ ∨ isOk s) (slotAt-shift A Θ (X ∸ d))
bfree-shift A Θ d `ℕ      = refl
bfree-shift A Θ d `𝔹      = refl
bfree-shift A Θ d (B ⇒ C) =
  cong₂ _∧_ (bfree-shift A Θ d B) (bfree-shift A Θ d C)
bfree-shift A Θ d (`∀ B)  = bfree-shift A Θ (suc d) B

rdSub-shift : ∀ A Θ j d k
  → rdSub (rvl A ∷ shiftReps Θ) (suc j) d k
    ≡ renameᵗ suc (rdSub Θ j d k)
rdSub-shift A Θ j d k with dec-< k d
rdSub-shift A Θ j d k | inj₁ lt =
  trans (rdSub-lo (rvl A ∷ shiftReps Θ) (suc j) d k lt)
        (cong (renameᵗ suc) (sym (rdSub-lo Θ j d k lt)))
rdSub-shift A Θ j d k | inj₂ ¬lt =
  trans (cong (rdSub (rvl A ∷ shiftReps Θ) (suc j) d) (sym idx))
    (trans (rdSub-hi (rvl A ∷ shiftReps Θ) (suc j) d (k ∸ d))
      (trans (cong₂ (λ r c → γcnc r c (shiftReps Θ) (k ∸ d))
                    (cong suc (revs-shiftReps Θ)) (cmax-shiftReps Θ))
        (trans (γcnc-shift (revs Θ) (cmax Θ) Θ (k ∸ d))
          (cong (renameᵗ suc)
                (trans (sym (rdSub-hi Θ j d (k ∸ d)))
                       (cong (rdSub Θ j d) idx))))))
  where idx : d + (k ∸ d) ≡ k
        idx = m+[n∸m]≡n (≤-pred (≰⇒> ¬lt))

rawRead-shift : ∀ A Θ j d A₁
  → rawRead (rvl A ∷ shiftReps Θ) (suc j) d A₁
    ≡ renameᵗ suc (rawRead Θ j d A₁)
rawRead-shift A Θ j d A₁ =
  trans (subst-cong (rdSub-shift A Θ j d) A₁)
        (sym (rename-subst suc (rdSub Θ j d) A₁))

dfree-shift : ∀ j b T
  → dfree b (suc (suc j)) (renameᵗ (liftⁿ b suc) T) ≡ dfree b (suc j) T
dfree-shift j b (` X) with split b X
dfree-shift j b (` X) | inj₁ lt
  rewrite liftⁿ-lo b suc X lt | ⌊⌋-of (X <? b) lt = refl
dfree-shift j b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b suc i =
  cong₂ _∨_
    (trans (⌊⌋-false ((b + suc i) <? b) (m+n≮m b (suc i)))
           (sym (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
    (⌊⌋-iff ((b + suc (suc j)) ≤? (b + suc i))
            ((b + suc j) ≤? (b + i)) fwd bwd)
  where
    fwd : b + suc (suc j) ≤ b + suc i → b + suc j ≤ b + i
    fwd le = +-monoʳ-≤ b (≤-pred (+-cancelˡ-≤ b _ _ le))
    bwd : b + suc j ≤ b + i → b + suc (suc j) ≤ b + suc i
    bwd le = +-monoʳ-≤ b (s≤s (+-cancelˡ-≤ b _ _ le))
dfree-shift j b `ℕ      = refl
dfree-shift j b `𝔹      = refl
dfree-shift j b (T ⇒ U) =
  cong₂ _∧_ (dfree-shift j b T) (dfree-shift j b U)
dfree-shift j b (`∀ T)  = dfree-shift j (suc b) T

dnT-shift : ∀ j b T
  → renameᵗ (liftⁿ b (_∸ suc (suc j))) (renameᵗ (liftⁿ b suc) T)
    ≡ renameᵗ (liftⁿ b (_∸ suc j)) T
dnT-shift j b (` X) with split b X
dnT-shift j b (` X) | inj₁ lt
  rewrite liftⁿ-lo b suc X lt
        | liftⁿ-lo b (_∸ suc (suc j)) X lt
        | liftⁿ-lo b (_∸ suc j) X lt = refl
dnT-shift j b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b suc i
        | liftⁿ-hi b (_∸ suc (suc j)) (suc i)
        | liftⁿ-hi b (_∸ suc j) i = refl
dnT-shift j b `ℕ      = refl
dnT-shift j b `𝔹      = refl
dnT-shift j b (T ⇒ U) =
  cong₂ _⇒_ (dnT-shift j b T) (dnT-shift j b U)
dnT-shift j b (`∀ T)  = cong `∀ (dnT-shift j (suc b) T)

⟦⟧-shift : ∀ A Θ j d A₁
  → ⟦ rvl A ∷ shiftReps Θ ⟧ᵉ (suc j) d A₁ ≡ ⟦ Θ ⟧ᵉ j d A₁
⟦⟧-shift A Θ j d A₁
  rewrite bfree-shift A Θ d A₁ | rawRead-shift A Θ j d A₁
        | dfree-shift j 0 (rawRead Θ j d A₁)
        | dnT-shift j 0 (rawRead Θ j d A₁) = refl

revEnts-shift : ∀ A Θ j Ξ
  → revEnts (rvl A ∷ shiftReps Θ) (suc j) (shiftReps Ξ)
    ≡ revEnts Θ j Ξ
revEnts-shift A Θ j []            = refl
revEnts-shift A Θ j (rvl B ∷ Ξ)   =
  cong₂ _∷_ hd (revEnts-shift A Θ (suc j) Ξ)
  where
    hd : ⟦ rvl A ∷ shiftReps Θ ⟧ᵉ (suc j) (revs (shiftReps Ξ)) B
         ≡ ⟦ Θ ⟧ᵉ j (revs Ξ) B
    hd rewrite revs-shiftReps Ξ = ⟦⟧-shift A Θ j (revs Ξ) B
revEnts-shift A Θ j (rvl⋆ ∷ Ξ)    =
  cong (abst ∷_) (revEnts-shift A Θ (suc j) Ξ)
revEnts-shift A Θ j (cnc X B ∷ Ξ) = revEnts-shift A Θ j Ξ

-- the interior of the shifted boundary is the old one, with the new
-- reveal's own knowledge entry on top
intOf-shift : ∀ (Γ : TCtx) A Θ
  → intOf Γ (rvl A ∷ shiftReps Θ)
    ≡ ⟦ rvl A ∷ shiftReps Θ ⟧ᵉ 0 (revs Θ) A ∷ intOf Γ Θ
intOf-shift Γ A Θ
  rewrite revs-shiftReps Θ | cmax-shiftReps Θ =
  cong (λ Ψ → ⟦ rvl A ∷ shiftReps Θ ⟧ᵉ 0 (revs Θ) A
              ∷ (Ψ ++ dropN (cmax Θ) Γ))
       (revEnts-shift A Θ 0 Θ)

-- … so R1's boundary is well formed at the interior (env) uses
bwf-shift : ∀ {Δ A} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → prepAbst (revs Θ) Δ ⊢ A
  → Δ ∣ intOf Δ (rvl A ∷ shiftReps Θ) ⊢ᵇ (rvl A ∷ shiftReps Θ)
bwf-shift {Δ} {A} Θ bwf wfA =
  subst (λ Ψ → Bwf Δ Ψ (rvl A ∷ shiftReps Θ) (rvl A ∷ shiftReps Θ))
        (sym (intOf-shift Δ A Θ))
        (bwf↑ (subst (λ r → prepAbst r Δ ⊢ A)
                     (sym (revs-shiftReps Θ)) wfA)
              (bwf-shiftReps (⟦ rvl A ∷ shiftReps Θ ⟧ᵉ 0 (revs Θ) A)
                             Θ Θ bwf))

-- TyWrap's own premise: the LIFTED type argument is well formed over the
-- exterior extended by the boundary's existing reveal slots
wf-lift : ∀ {Δ A} Θ → Δ ⊢ A → prepAbst (revs Θ) Δ ⊢ renameᵗ (revs Θ +_) A
wf-lift {Δ} Θ wfA =
  wf-ren (λ {X} p → prepAbst-hi (revs Θ) Δ X p) wfA

