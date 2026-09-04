module strong.notes.old.Example8Trace where

-- SUPERSEDED 2026-09-04 by the ambient-dual install (knowledge
-- interiors, reversal-form conceal, telescopic reveal block,
-- Γ-indexed reduction with dualᴳ).  The surviving content — the
-- bad/bad₂ refutations, the face laws, the dual's read-back — now
-- lives in strong.Boundary / strong.BReduction; this file is kept as
-- a record of the design path and does NOT compile against the
-- current core.


-- DESIGN VERIFICATION (not part of the development).  Example 8 of
-- notes.md — the OLD design's preservation counterexample — replayed as a
-- FULL trace from the closed source program, with every term typed at
--   [] ∣ [] ⊢ Tᵢ ⦂ `∀ (` 0 ⇒ ` 0)   (= ∀Y. Y→Y).
--
--   (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)   :   ∀Y. Y→Y
--
-- Verdict, in one paragraph.  R1 and R1′ BOTH work on Example 8, on the
-- full trace, not just on the redex: T0 … T5 and T4′ all type at
-- `∀ (` 0 ⇒ ` 0).  They differ only in the SHAPE of the contractum.
--
--   R1  floats the type application inside the boundary and applies it to
--       the FRESH reveal variable Z (` 0), recording the old type argument
--       Y as the reveal REP (exterior).  Contractum T4; its interior then
--       TyBeta-steps (a real rule) to T5, which carries a NESTED wrapper
--         ((ƛ ` 0 ∙ ` 0) ⟪ ↑Z′:=Z , Z′→Z′ ⟫) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫.
--       Both wrappers type: the inner one lives over the outer's interior
--       [Z], and its reveal rep ` 0 IS Z, read in that exterior.
--   R1′ combines directly: T4′ = (ƛ ` 0 ∙ ` 0) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫ —
--       one boundary, no ⇑ᵀ, no nesting.  Same type.
--
-- Why neither fails where the old design did.  The new boundary is
--   rvl (` 0) ∷ cnc 1 `ℕ ∷ []   over   Δ8 = [Y(0) , X(1)],
-- whose interior is prepAbst 1 (dropN 2 Δ8) = [Z] — Y is NOT in it.  Y is
-- BLOCKED in the interior (baseS Θ8 Δ8 = blk ∷ ok ∷ []) and appears only
-- as the reveal rep, which `env`'s bwf↑ reads in the EXTERIOR Δ8.  The old
-- design's TyWrapCncl instead pushed the type argument into the sealed
-- body — F [C[X:=A]] with C = Y and Y[X:=ℕ] = Y — so the conceal body was
-- typed in Δ↓X = ∅ while mentioning Y: untypable.  Recording Y as an
-- exterior reveal rep, rather than substituting it inward, is exactly the
-- fix.
--
-- Steps that are REAL rules of strong.BReduction are given as `-→`
-- derivations.  R1 (TyWrap) and R2 (Wrap) are not yet rules, so for
-- T1→T2 and T3→T4 only the two typings are given (checked at line 1 of
-- this file's date: BReduction exports no TyWrap).
--
-- Imports: Types, Context, Boundary, BReduction only.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
  using (TCtx; abst; rvld; _⊢_; wf-var; wf-ℕ; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         Ctx; _∋_⦂_; here; there; ⤊)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; _-→_;
         TyBeta; Beta; ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫; ⇑ᵀ; _[_]ᵐ)

------------------------------------------------------------------------
-- 0.  Types, boundaries, and the source term
------------------------------------------------------------------------

∀ZZ : Ty                        -- ∀Z. Z→Z   (also ∀Y. Y→Y : same syntax)
∀ZZ = `∀ (` 0 ⇒ ` 0)

Bfun : Ty                       -- the ∀-body of ΛX : (∀Z.Z→Z) ⇒ ∀Y.Y→Y
Bfun = ∀ZZ ⇒ ∀ZZ                -- X does not occur

polyid : Term                   -- ΛZ. λz:Z. z
polyid = Λ (ƛ ` 0 ∙ ` 0)

-- ΛY. f [Y]   :  under ΛX then ΛY, so X = ` 1, Y = ` 0, and f = ` 0 (term)
body8 : Term
body8 = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])

src : Term                      -- ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]
src = Λ (ƛ ∀ZZ ∙ body8)

-- the boundaries that occur along the trace
Θr : BCtx                       -- ↑X:=ℕ   (born at the first TyBeta)
Θr = rvl `ℕ ∷ []

Θc : BCtx                       -- ↓X:=ℕ   (the dual, wrapping the argument)
Θc = cnc 0 `ℕ ∷ []

Θ8 : BCtx                       -- ↓X:=ℕ after ⇑ᵀ : X is now Γ-index 1
Θ8 = cnc 1 `ℕ ∷ []

-- shiftReps of BoundaryRules.md §1 (conceal reps only), re-derived here
shiftReps : BCtx → BCtx
shiftReps []            = []
shiftReps (rvl A   ∷ Θ) = rvl A ∷ shiftReps Θ
shiftReps (cnc X A ∷ Θ) = cnc X (renameᵗ suc A) ∷ shiftReps Θ

Θn : BCtx                       -- R1/R1′'s new boundary : ↑Z:=Y , ↓X:=ℕ
Θn = rvl (` 0) ∷ shiftReps Θ8

_ : Θn ≡ rvl (` 0) ∷ cnc 1 `ℕ ∷ []
_ = refl

Θi : BCtx                       -- the inner boundary TyBeta mints inside T4
Θi = rvl (` 0) ∷ []

------------------------------------------------------------------------
-- The two contexts that matter, and their interiors
------------------------------------------------------------------------

Δ1 : TCtx                       -- interior of the outer ↑X:=ℕ boundary : [X]
Δ1 = abst ∷ []

Δ8 : TCtx                       -- under the Λ inside it : [Y(0) , X(1)]
Δ8 = abst ∷ abst ∷ []

_ : intOf [] Θr ≡ Δ1
_ = refl

_ : intOf Δ1 Θc ≡ []
_ = refl

_ : intOf Δ8 Θ8 ≡ []
_ = refl

-- Y is BLOCKED in Θ8's interior — this is what killed the old design
_ : baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []
_ = refl

-- R1's new boundary keeps Y out of the interior: interior = [Z]
_ : intOf Δ8 Θn ≡ abst ∷ []
_ = refl

_ : baseS Θn Δ8 ≡ ok ∷ blk ∷ ok ∷ []
_ = refl

-- the inner boundary of T5 lives over that [Z]
_ : intOf (abst ∷ []) Θi ≡ abst ∷ abst ∷ []
_ = refl

------------------------------------------------------------------------
-- 1.  T0 — the closed source program
------------------------------------------------------------------------

T0 : Term
T0 = (src ·[ Bfun , `ℕ ]) · polyid

⊢polyid : ∀ {Δ Γₜ} → Δ ∣ Γₜ ⊢ polyid ⦂ ∀ZZ
⊢polyid = ⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))

⊢∀ZZ : ∀ {Δ} → Δ ⊢ ∀ZZ
⊢∀ZZ = wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst))

-- λf:(∀Z.Z→Z). ΛY. f [Y]  types in any Δ that has at least one variable;
-- we need it at Δ1 (inside the ↑X:=ℕ boundary) and under the raw Λ.
⊢lam8 : ∀ {Δ} → Δ ∣ [] ⊢ (ƛ ∀ZZ ∙ body8) ⦂ Bfun
⊢lam8 = ⊢ƛ ⊢∀ZZ (⊢Λ (⊢·[] (⊢` here) (wf-var here-abst)))

⊢T0 : [] ∣ [] ⊢ T0 ⦂ ∀ZZ
⊢T0 = ⊢· (⊢·[] (⊢Λ ⊢lam8) wf-ℕ) ⊢polyid

------------------------------------------------------------------------
-- 2.  T1 — by TyBeta (a real rule).  The boundary is BORN.
------------------------------------------------------------------------

T1 : Term
T1 = ((ƛ ∀ZZ ∙ body8) ⟪ Θr , Bfun ⟫) · polyid

_ : T0 -→ T1
_ = ξ-·-l (TyBeta (V-G G-ƛ))

⊢T1 : [] ∣ [] ⊢ T1 ⦂ ∀ZZ
⊢T1 = ⊢· (env (bwf↑ wf-ℕ bwf[])
              (sc-⇒ (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
                    (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))))
              ⊢lam8)
         ⊢polyid

------------------------------------------------------------------------
-- 3.  T2 — by R2 (NOT a rule yet; both sides typed).  The argument is
--     pushed inside through the DUAL boundary  dualᵇ Θr = ↓X:=ℕ = Θc.
------------------------------------------------------------------------

W2 : Term                       -- the argument, wrapped in the dual
W2 = polyid ⟪ Θc , ∀ZZ ⟫

T2 : Term
T2 = ((ƛ ∀ZZ ∙ body8) · W2) ⟪ Θr , ∀ZZ ⟫

⊢W2 : Δ1 ∣ [] ⊢ W2 ⦂ ∀ZZ
⊢W2 = env (bwf↓ here-abst wf-ℕ bwf[])
          (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
          ⊢polyid

⊢T2 : [] ∣ [] ⊢ T2 ⦂ ∀ZZ
⊢T2 = env (bwf↑ wf-ℕ bwf[])
          (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
          (⊢· ⊢lam8 ⊢W2)

------------------------------------------------------------------------
-- 4.  T3 — by ξ-⟪⟫ (Beta …) (real rules).  The substitution is performed
--     FOR REAL: ⇑ᵀ moves the wrapped argument under the Λ, and the
--     conceal index 0 (X) really does become 1 — checked by refl below,
--     not assumed.  That is the probe's Θ8.
------------------------------------------------------------------------

W3 : Term
W3 = polyid ⟪ Θ8 , ∀ZZ ⟫

T3 : Term
T3 = (Λ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ])) ⟪ Θr , ∀ZZ ⟫

-- the ⇑ᵀ shift of the conceal index, computed
_ : ⇑ᵀ W2 ≡ W3
_ = refl

-- T3's interior IS the substᵀᵐ result — literally, by refl
_ : body8 [ W2 ]ᵐ ≡ Λ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ])
_ = refl

⊢W2-value : Value W2
⊢W2-value = V-⟪⟫ (V-G (G-Λ (V-G G-ƛ)))

_ : T2 -→ T3
_ = ξ-⟪⟫ (Beta ⊢W2-value)

-- the R1 REDEX, at Δ8, with Y (` 0) as the type argument
⊢redex : Δ8 ∣ [] ⊢ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ]) ⦂ (` 0 ⇒ ` 0)
⊢redex =
  ⊢·[] (env (bwf↓ (skip-abst here-abst) wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            ⊢polyid)
       (wf-var here-abst)

⊢T3 : [] ∣ [] ⊢ T3 ⦂ ∀ZZ
⊢T3 = env (bwf↑ wf-ℕ bwf[])
          (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
          (⊢Λ ⊢redex)

------------------------------------------------------------------------
-- 5.  T4 — the R1 contractum (NOT a rule yet; both sides typed).
--
--     ((⇑ᵀ polyid) ·[ Z→Z , ` 0 ]) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫
--
--     The floated application applies polyid to the FRESH interior
--     variable Z (` 0 of intOf Δ8 Θn = [Z]) — NOT to Y.  Y survives only
--     as the reveal rep of ↑Z:=Y, which bwf↑ reads in the exterior Δ8.
--     Y is blocked in the interior (baseS Θn Δ8 = ok ∷ blk ∷ ok ∷ []) and
--     is never named there.  polyid is closed, so ⇑ᵀ polyid = polyid.
------------------------------------------------------------------------

_ : ⇑ᵀ polyid ≡ polyid
_ = refl

R1body : Term
R1body = (polyid ·[ ` 0 ⇒ ` 0 , ` 0 ]) ⟪ Θn , ` 0 ⇒ ` 0 ⟫

T4 : Term
T4 = (Λ R1body) ⟪ Θr , ∀ZZ ⟫

-- both faces of the new boundary, computed
_ : substᵗ (γᵇ Θn) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)     -- internal : Z→Z
_ = refl

_ : substᵗ (ρᵇ Θn) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)     -- external : Y→Y
_ = refl

⊢R1body : Δ8 ∣ [] ⊢ R1body ⦂ (` 0 ⇒ ` 0)
⊢R1body =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢·[] ⊢polyid (wf-var here-abst))

⊢T4 : [] ∣ [] ⊢ T4 ⦂ ∀ZZ
⊢T4 = env (bwf↑ wf-ℕ bwf[])
          (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
          (⊢Λ ⊢R1body)

------------------------------------------------------------------------
-- 6.  T5 — TyBeta INSIDE T4 (a real rule).  A NESTED wrapper appears.
--
--     ((ƛ ` 0 ∙ ` 0) ⟪ ↑Z′:=Z , Z′→Z′ ⟫) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫
--
--     The inner boundary's exterior is intOf Δ8 Θn = [Z]; its reveal rep
--     ` 0 IS Z, read in that exterior; its interior is [Z′ , Z].
------------------------------------------------------------------------

T5body : Term
T5body = ((ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫) ⟪ Θn , ` 0 ⇒ ` 0 ⟫

T5 : Term
T5 = (Λ T5body) ⟪ Θr , ∀ZZ ⟫

_ : T4 -→ T5
_ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (TyBeta (V-G G-ƛ))))

-- the inner wrapper, typed over the OUTER's interior [Z]
⊢inner : (abst ∷ []) ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫
                          ⦂ (` 0 ⇒ ` 0)
⊢inner = env (bwf↑ (wf-var here-abst) bwf[])
             (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
             (⊢ƛ (wf-var here-abst) (⊢` here))

⊢T5body : Δ8 ∣ [] ⊢ T5body ⦂ (` 0 ⇒ ` 0)
⊢T5body =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      ⊢inner

⊢T5 : [] ∣ [] ⊢ T5 ⦂ ∀ZZ
⊢T5 = env (bwf↑ wf-ℕ bwf[])
          (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
          (⊢Λ ⊢T5body)

------------------------------------------------------------------------
-- 7.  T4′ — the R1′ contractum, in T3's place: ONE boundary, no ⇑ᵀ,
--     no nesting.  Same context, same type as T4 and T5.
------------------------------------------------------------------------

T4′ : Term
T4′ = (Λ ((ƛ ` 0 ∙ ` 0) ⟪ Θn , ` 0 ⇒ ` 0 ⟫)) ⟪ Θr , ∀ZZ ⟫

⊢R1′body : Δ8 ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θn , ` 0 ⇒ ` 0 ⟫) ⦂ (` 0 ⇒ ` 0)
⊢R1′body =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-abst) (⊢` here))

⊢T4′ : [] ∣ [] ⊢ T4′ ⦂ ∀ZZ
⊢T4′ = env (bwf↑ wf-ℕ bwf[])
           (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
           (⊢Λ ⊢R1′body)

------------------------------------------------------------------------
-- 8.  Summary of the trace (all at  [] ∣ [] ⊢ _ ⦂ ∀ZZ)
--
--   T0  -→ (ξ-·-l (TyBeta …))          T1
--   T1  ⇝  (R2, not a rule)         T2
--   T2  -→ (ξ-⟪⟫ (Beta …))           T3
--   T3  ⇝  (R1, not a rule)         T4     ⇝ (R1′) T4′
--   T4  -→ (ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ TyBeta)))  T5
--
-- No step is ill-typed.  T5 and T4′ are the two candidate normal forms;
-- R1′'s is the tighter of the two, and R1's differs from it only by the
-- extra inner ↑Z′:=Z boundary, which a Cancel/Merge rule would remove.
------------------------------------------------------------------------
