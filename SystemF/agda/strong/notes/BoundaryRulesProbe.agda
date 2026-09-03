module strong.notes.BoundaryRulesProbe where

-- DESIGN PROBE (not part of the development).  Candidate boundary-
-- manipulation rules for the combined boundary  M ⟪ Θ , B₀ ⟫  (PLAN §4),
-- with their typing machine-checked on examples, plus the canonical-forms
-- material progress needs (PLAN §5).  The decision memo that reads this
-- file is notes/BoundaryRules.md.
--
-- Imports only the stable modules (Types / TypeSubst / Context / Weakening
-- / Boundary).  A few helpers that also exist in BReduction.agda
-- (prepId-lo, prepId-hi, split) are RE-DERIVED here because BReduction is
-- being edited concurrently and still has holes; nothing below depends on
-- it.  No postulates, no holes.
--
-- Naming of the candidate rules (used in the memo):
--   R1  TyWrap   a boundary meets a type application
--   R2  Wrap     a boundary meets an application (needs the dual dualᵇ)
--   R3  β-drop    V ⟪ [] , B₀ ⟫ -→ V
--   R4  β-cancel  a reveal cancelled against a matching conceal
--   R1′ TyBeta⟪⟫     the "direct combine" variant of R1 (body must be Λ V)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_; _⊔_)
open import Data.Nat.Properties using (_≟_; m+n∸m≡n; m+n≮m; ≰⇒>)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (¬_; yes; no; Dec; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; subst-id; exts-sub-cons; rename-subst-commute;
         cons-sub)
open import strong.Context
  using (TCtx; abst; rvld; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         Ctx; _∋_⦂_; here; there; ⤊)
open import strong.Weakening using (wf-⇑-abst)
open import strong.Boundary

------------------------------------------------------------------------
-- 0.  Index plumbing (re-derived; cf. BReduction.agda)
------------------------------------------------------------------------

prepId-lo : ∀ r (σ : Substᵗ) X → X < r → prepId r σ X ≡ ` X
prepId-lo r σ X X<r with X <? r
prepId-lo r σ X X<r | yes _   = refl
prepId-lo r σ X X<r | no ¬X<r = ⊥-elim (¬X<r X<r)

prepId-hi : ∀ r (σ : Substᵗ) i → prepId r σ (r + i) ≡ σ i
prepId-hi r σ i with (r + i) <? r
prepId-hi r σ i | yes lt = ⊥-elim (m+n≮m r i lt)
prepId-hi r σ i | no  _  = cong σ (m+n∸m≡n r i)

split : ∀ r X → (X < r) ⊎ (Σ ℕ λ i → X ≡ r + i)
split zero    X       = inj₂ (X , refl)
split (suc r) zero    = inj₁ (s≤s z≤n)
split (suc r) (suc X) with split r X
split (suc r) (suc X) | inj₁ X<r        = inj₁ (s≤s X<r)
split (suc r) (suc X) | inj₂ (i , X≡ri) = inj₂ (i , cong suc X≡ri)

-- the exterior face is the identity on the Γ-part of the boundary frame
ρᵇ-hi : ∀ Θ i → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-hi []              i = refl
ρᵇ-hi (rvl A   ∷ Θ)  i = ρᵇ-hi Θ i
ρᵇ-hi (cnc X A ∷ Θ)  i = ρᵇ-hi Θ i

-- the interior face is the identity on the reveal variables: a reveal is
-- ABSTRACT inside.  (Used by the canonical-forms discussion in §6.)
γᵇ-lo : ∀ Θ X → X < revs Θ → γᵇ Θ X ≡ ` X
γᵇ-lo Θ X X<r = prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X X<r

------------------------------------------------------------------------
-- 1.  R1 (and R1′): a boundary meets a TYPE APPLICATION
--
--   (V ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
--     -→ ((⇑ᵀ V) ·[ substᵗ (extsᵗ (γᵇ Θ)) B₀ , ` 0 ])
--          ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫                            (R1)
--     -→ V′ ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫       when V = Λ V′       (R1′)
--
-- The interior gains ONE fresh abstract variable (prepAbst grows by one),
-- so the conceal reps of Θ — which live over the WHOLE interior — must be
-- shifted: that is `shiftReps`.  The two face laws below are what makes
-- the contractum type-check; γᵇ-shift is proved for ALL slots (the blocked
-- ones included), so R1 needs no scope side-condition of its own.
------------------------------------------------------------------------

shiftReps : BCtx → BCtx
shiftReps []             = []
shiftReps (rvl A   ∷ Θ) = rvl A ∷ shiftReps Θ
shiftReps (cnc X A ∷ Θ) = cnc X (renameᵗ suc A) ∷ shiftReps Θ

revs-shift : ∀ Θ → revs (shiftReps Θ) ≡ revs Θ
revs-shift []             = refl
revs-shift (rvl A   ∷ Θ) = cong suc (revs-shift Θ)
revs-shift (cnc X A ∷ Θ) = revs-shift Θ

cmax-shift : ∀ Θ → cmax (shiftReps Θ) ≡ cmax Θ
cmax-shift []             = refl
cmax-shift (rvl A   ∷ Θ) = cmax-shift Θ
cmax-shift (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-shift Θ)

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
        (cong (renameᵗ suc)
              (sym (prepId-lo r (γcnc r c Θ) j j<r)))
γᵇ-shift-raw r c Θ (suc j) | inj₂ (i , refl) =
  trans (prepId-hi (suc r) (γcnc (suc r) c (shiftReps Θ)) i)
        (trans (γcnc-shift r c Θ i)
               (cong (renameᵗ suc) (sym (prepId-hi r (γcnc r c Θ) i))))

-- FACE LAW (interior).  Adding the reveal of the type argument and
-- shifting the conceal reps is exactly `extsᵗ` on the interior face.
γᵇ-shift : ∀ A Θ X → γᵇ (rvl A ∷ shiftReps Θ) X ≡ extsᵗ (γᵇ Θ) X
γᵇ-shift A Θ X rewrite revs-shift Θ | cmax-shift Θ =
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

-- the B index of  ·[ B , A ]  is FORCED by the wrapper's boundary type
tapp-B-forced : ∀ Θ B₀ {B} → substᵗ (ρᵇ Θ) (`∀ B₀) ≡ `∀ B
              → B ≡ substᵗ (extsᵗ (ρᵇ Θ)) B₀
tapp-B-forced Θ B₀ refl = refl

-- the boundary stays well formed once the interior gains an abstract var
bwf-shift : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ Θ → Δ ∣ (abst ∷ Ψ) ⊢ᵇ shiftReps Θ
bwf-shift []             bwf[]              = bwf[]
bwf-shift (rvl A   ∷ Θ) (bwf↑ wfA bwf)     = bwf↑ wfA (bwf-shift Θ bwf)
bwf-shift (cnc X A ∷ Θ) (bwf↓ p wfA bwf)   =
  bwf↓ p (wf-⇑-abst wfA) (bwf-shift Θ bwf)

-- the scope stack just gains one accessible slot for the new reveal, so
-- R1's Scoped obligation is exactly the sc-∀ inversion of the redex's
slotAt-shift : ∀ A Θ i → slotAt (rvl A ∷ shiftReps Θ) i ≡ slotAt Θ i
slotAt-shift A Θ i with cmax (shiftReps Θ) ≤? i | cmax Θ ≤? i
slotAt-shift A Θ i | yes _ | yes _ = refl
slotAt-shift A Θ i | yes p | no ¬q =
  ⊥-elim (¬q (subst (_≤ i) (cmax-shift Θ) p))
slotAt-shift A Θ i | no ¬p | yes q =
  ⊥-elim (¬p (subst (_≤ i) (sym (cmax-shift Θ)) q))
slotAt-shift A Θ i | no _  | no _ rewrite isConc-shift i Θ = refl

slotsᴳ-shift : ∀ A Θ k (Γ : TCtx)
  → slotsᴳ (rvl A ∷ shiftReps Θ) k Γ ≡ slotsᴳ Θ k Γ
slotsᴳ-shift A Θ k []      = refl
slotsᴳ-shift A Θ k (E ∷ Γ) =
  cong₂ _∷_ (slotAt-shift A Θ k) (slotsᴳ-shift A Θ (suc k) Γ)

baseS-shift : ∀ A Θ (Γ : TCtx)
  → baseS (rvl A ∷ shiftReps Θ) Γ ≡ ok ∷ baseS Θ Γ
baseS-shift A Θ Γ rewrite revs-shift Θ =
  cong (ok ∷_) (cong (repl-ok (revs Θ) ++_) (slotsᴳ-shift A Θ 0 Γ))

-- the small law R1 needs on the FLOATED type application:
--   the fresh variable put back for the one that ⇑ᵀ made room for
ext-suc-[]0 : ∀ T → (renameᵗ (extᵗ suc) T) [ ` 0 ]ᵗ ≡ T
ext-suc-[]0 T =
  trans (rename-subst-commute (extᵗ suc) (singleTyEnv (` 0)) T)
        (trans (subst-cong h T) (subst-id T))
  where
    h : ∀ X → singleTyEnv (` 0) (extᵗ suc X) ≡ ` X
    h zero    = refl
    h (suc j) = refl

------------------------------------------------------------------------
-- 2.  R1 / R1′ on the NEW-DESIGN ANALOGUE OF EXAMPLE 8
--
-- Example 8 (notes/Scratch7-9) is the closed program whose 4th step made
-- the OLD design ill-typed: a value concealed on X (index 1) is TYPE-
-- APPLIED to the shallower Λ-bound Y (index 0).  Under the combined
-- boundary the same redex steps to a WELL-TYPED term, because the type
-- argument Y is recorded as a REVEAL rep (which is read in the exterior)
-- instead of being pushed into the interior, where Y is blocked.
------------------------------------------------------------------------

polyid : Term
polyid = Λ (ƛ ` 0 ∙ ` 0)

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

-- exterior of the redex:  Y (Λ-bound, index 0), X (revealed, index 1)
Δ8 : TCtx
Δ8 = abst ∷ abst ∷ []

Θ8 : BCtx                       -- conceal X (index 1), rep ℕ
Θ8 = cnc 1 `ℕ ∷ []

_ : intOf Δ8 Θ8 ≡ []
_ = refl

_ : baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []          -- Y is BLOCKED inside
_ = refl

-- the redex   (polyid ⟪ ↓X:=ℕ , ∀(Z→Z) ⟫) [Z→Z , Y]   :  Y → Y
⊢redex-R1 : Δ8 ∣ [] ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                      ⦂ (` 0 ⇒ ` 0)
⊢redex-R1 =
  ⊢·[] (env (bwf↓ (skip-abst here-abst) wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-abst)

-- R1′ (direct combine):  the ∀-body becomes the new boundary type and the
-- type argument Y becomes a REVEAL rep.  Well typed at the SAME type.
⊢contractum-R1′ :
  Δ8 ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1′ =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-abst) (⊢` here))

-- R1 (float the type application inside, applied to the fresh reveal
-- variable ` 0).  Also well typed at the same type — and it does NOT need
-- the body to be syntactically a Λ.
⊢contractum-R1 :
  Δ8 ∣ [] ⊢ (polyid ·[ ` 0 ⇒ ` 0 , ` 0 ])
              ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1 =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) (wf-var here-abst))

-- the ·[ B , A ] index of the redex is forced (tapp-B-forced), here to
-- substᵗ (extsᵗ (ρᵇ Θ8)) (` 0 ⇒ ` 0) = ` 0 ⇒ ` 0
_ : substᵗ (extsᵗ (ρᵇ Θ8)) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)
_ = refl

-- the interior type of R1's floated application, computed:  ` 0 ⇒ ` 0
_ : substᵗ (extsᵗ (γᵇ Θ8)) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)
_ = refl

-- and the two faces of the NEW boundary agree with the face laws
_ : substᵗ (γᵇ (rvl (` 0) ∷ shiftReps Θ8)) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)
_ = refl

_ : substᵗ (ρᵇ (rvl (` 0) ∷ shiftReps Θ8)) (` 0 ⇒ ` 0) ≡ (` 0 ⇒ ` 0)
_ = refl

------------------------------------------------------------------------
-- 3.  The DUAL boundary  dualᵇ  (for R2)
--
--   Θ  : exterior Δ , interior  intOf Δ Θ = prepAbst r (dropN c Δ)
--   Θᵈ : exterior intOf Δ Θ , interior  Δ           (r = revs Θ, c = cmax Θ)
--
-- Construction: every reveal of Θ becomes a CONCEAL of Θᵈ (its rep, which
-- is read in Δ = Θᵈ's interior, is exactly a conceal rep); every Δ-slot
-- that Θ dropped (indices 0 … c-1) becomes a REVEAL of Θᵈ whose rep is
-- Θ's conceal rep for that slot (read in intOf Δ Θ = Θᵈ's exterior).
-- A dropped slot that is NOT concealed is BLOCKED, and has no meaning in
-- the interior: its reveal rep is arbitrary (`ℕ below).  That is sound
-- precisely because the (env) scope premise forbids B₀ from naming it.
------------------------------------------------------------------------

repOf : ℕ → BCtx → Ty
repOf i []             = `ℕ            -- blocked slot: arbitrary
repOf i (rvl A   ∷ Θ) = repOf i Θ
repOf i (cnc X A ∷ Θ) with i ≟ X
repOf i (cnc X A ∷ Θ) | yes _ = A
repOf i (cnc X A ∷ Θ) | no  _ = repOf i Θ

rvlsOf : ℕ → ℕ → BCtx → BCtx           -- k reveals, for slots i, i+1, …
rvlsOf zero    i Θ = []
rvlsOf (suc k) i Θ = rvl (repOf i Θ) ∷ rvlsOf k (suc i) Θ

cncOfRevs : ℕ → BCtx → BCtx            -- conceal each reveal var, at j, j+1, …
cncOfRevs j []             = []
cncOfRevs j (rvl A   ∷ Θ) = cnc j A ∷ cncOfRevs (suc j) Θ
cncOfRevs j (cnc X A ∷ Θ) = cncOfRevs j Θ

dualᵇ : BCtx → BCtx
dualᵇ Θ = rvlsOf (cmax Θ) 0 Θ ++ cncOfRevs 0 Θ

-- the boundary frames of Θ and Θᵈ hold the same slots in a different
-- order: [reveals of Θ][dropped Δ-slots][kept Δ-slots] becomes
-- [dropped Δ-slots][reveals of Θ][kept Δ-slots].
swapIdx : ℕ → ℕ → ℕ → ℕ                -- swapIdx r c X
swapIdx r c X with X <? r
swapIdx r c X | yes _ = c + X
swapIdx r c X | no  _ with (X ∸ r) <? c
swapIdx r c X | no _ | yes _ = X ∸ r
swapIdx r c X | no _ | no  _ = X

swapᵇ : BCtx → ℕ → ℕ
swapᵇ Θ = swapIdx (revs Θ) (cmax Θ)

------------------------------------------------------------------------
-- 3a.  dualᵇ checked on three boundaries: reveal-only, conceal-only
--      (the dual of the first) and MIXED.
------------------------------------------------------------------------

-- (i) reveal-only, over the empty exterior
Θr : BCtx
Θr = rvl `ℕ ∷ []

_ : intOf [] Θr ≡ abst ∷ []
_ = refl

_ : dualᵇ Θr ≡ cnc 0 `ℕ ∷ []
_ = refl

_ : intOf (intOf [] Θr) (dualᵇ Θr) ≡ []          -- round trip
_ = refl

-- the two face laws, pointwise on the one interesting slot (X = 0)
_ : ρᵇ (dualᵇ Θr) (swapᵇ Θr 0) ≡ γᵇ Θr 0
_ = refl

_ : γᵇ (dualᵇ Θr) (swapᵇ Θr 0) ≡ ρᵇ Θr 0
_ = refl

-- (ii) the dual is an involution here:  dualᵇ (dualᵇ Θr) = Θr
_ : dualᵇ (dualᵇ Θr) ≡ rvl `ℕ ∷ []
_ = refl

-- (iii) MIXED:  reveal Z:=ℕ and conceal X (index 1), over Δm = [Y , X]
Δm : TCtx
Δm = abst ∷ abst ∷ []

Θm : BCtx
Θm = rvl `ℕ ∷ cnc 1 `ℕ ∷ []

_ : intOf Δm Θm ≡ abst ∷ []                      -- interior = [Z]
_ = refl

_ : baseS Θm Δm ≡ ok ∷ blk ∷ ok ∷ []             -- Y is blocked
_ = refl

_ : dualᵇ Θm ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- the dual's interior is EXACTLY the original exterior …
_ : intOf (intOf Δm Θm) (dualᵇ Θm) ≡ Δm
_ = refl

-- … and its scope stack has NO blocked slot (so R2 never has to discharge
-- a scope obligation for the argument beyond the redex's own)
_ : baseS (dualᵇ Θm) (intOf Δm Θm) ≡ ok ∷ ok ∷ ok ∷ []
_ = refl

-- face laws at every slot of the mixed frame [Z , Y , X]:
--   Z (0)   : ok        — both laws hold
--   Y (1)   : BLOCKED   — the exterior law FAILS (see the witness below)
--   X (2)   : ok        — both laws hold
_ : ρᵇ (dualᵇ Θm) (swapᵇ Θm 0) ≡ γᵇ Θm 0
_ = refl

_ : γᵇ (dualᵇ Θm) (swapᵇ Θm 0) ≡ ρᵇ Θm 0
_ = refl

_ : ρᵇ (dualᵇ Θm) (swapᵇ Θm 2) ≡ γᵇ Θm 2
_ = refl

_ : γᵇ (dualᵇ Θm) (swapᵇ Θm 2) ≡ ρᵇ Θm 2
_ = refl

-- the FAILING slot, kept as a checked witness: at the blocked Y the two
-- sides really do differ (` 0 vs `ℕ), which is why R2 must appeal to the
-- (env) scope premise (subst-cong-sc) rather than to a pointwise identity.
_ : ρᵇ (dualᵇ Θm) (swapᵇ Θm 1) ≡ `ℕ
_ = refl

_ : γᵇ Θm 1 ≡ ` 1
_ = refl

blocked-slot-differs : ¬ (ρᵇ (dualᵇ Θm) (swapᵇ Θm 1) ≡ γᵇ Θm 1)
blocked-slot-differs ()

-- the interior law, by contrast, holds even at the blocked slot
_ : γᵇ (dualᵇ Θm) (swapᵇ Θm 1) ≡ ρᵇ Θm 1
_ = refl

-- dualᵇ is NOT literally an involution on a mixed boundary: the second
-- dual makes the blocked slot explicit (a conceal with the dummy rep).
-- The CONTEXTS still round-trip, which is all the rules need.
_ : dualᵇ (dualᵇ Θm) ≡ rvl `ℕ ∷ cnc 0 `ℕ ∷ cnc 1 `ℕ ∷ []
_ = refl

_ : intOf Δm (dualᵇ (dualᵇ Θm)) ≡ intOf Δm Θm
_ = refl

------------------------------------------------------------------------
-- 3b.  WHERE THE DUAL DOES NOT EXIST
--
-- intOf can only PREPEND fresh `abst` entries and DROP a prefix, so the
-- dual's interior is  prepAbst rᵈ (dropN cᵈ (intOf Δ Θ)).  When Δ's
-- dropped prefix contains a `rvld` entry it can never be rebuilt: no Θᵈ
-- has interior Γ₃ (Boundary.agda's three-revealed-variable context).
--
-- At RUNTIME this never bites: every context reachable from the empty one
-- is  prepAbst n []  (⊢Λ adds `abst`, intOf adds `abst`), i.e. all-abst,
-- and then prepAbst c (dropN c Δ) ≡ Δ.  `rvld` contexts only occur in
-- hand-written examples.
------------------------------------------------------------------------

dropN-nil : ∀ c → dropN c [] ≡ []
dropN-nil zero    = refl
dropN-nil (suc c) = refl

no-dual-raw : ∀ r c
  → prepAbst r (dropN c (rvld `ℕ ∷ [])) ≡ Γ₃ → ⊥
no-dual-raw zero    zero    ()
no-dual-raw zero    (suc c) eq with trans (sym (dropN-nil c)) eq
no-dual-raw zero    (suc c) eq | ()
no-dual-raw (suc r) zero    ()
no-dual-raw (suc r) (suc c) ()

no-dual-Γ₃ : ¬ (Σ BCtx λ Θᵈ → intOf (intOf Γ₃ Θ₃) Θᵈ ≡ Γ₃)
no-dual-Γ₃ (Θᵈ , eq) = no-dual-raw (revs Θᵈ) (cmax Θᵈ) eq

------------------------------------------------------------------------
-- 4.  R2: a boundary meets an APPLICATION
--
--   (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
--     -→ (V · (W ⟪ dualᵇ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
--
-- The argument, which lives in the exterior Δ, is moved inside by the
-- DUAL boundary; no term substitution and no ⇑ᵀ is involved, and V need
-- not be syntactically a ƛ (Beta fires afterwards, inside).
------------------------------------------------------------------------

-- 4a. reveal-only Θ, at the empty exterior — Example 8's second step.
fn : Term
fn = ƛ ∀ZZ ∙ (Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ]))

⊢redex-R2 : [] ∣ [] ⊢ (fn ⟪ Θr , ∀ZZ ⇒ ∀ZZ ⟫) · polyid ⦂ ∀ZZ
⊢redex-R2 =
  ⊢· (env (bwf↑ wf-ℕ bwf[])
          (sc-⇒ (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
                (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))))
          (⊢ƛ (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst)))
              (⊢Λ (⊢·[] (⊢` here) (wf-var here-abst)))))
     (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here)))

_ : swapᵇ Θr 0 ≡ 0                     -- reveal-only: the swap is trivial
_ = refl

⊢contractum-R2 :
  [] ∣ [] ⊢ (fn · (polyid ⟪ dualᵇ Θr , ∀ZZ ⟫)) ⟪ Θr , ∀ZZ ⟫ ⦂ ∀ZZ
⊢contractum-R2 =
  env (bwf↑ wf-ℕ bwf[])
      (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
      (⊢· (⊢ƛ (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst)))
              (⊢Λ (⊢·[] (⊢` here) (wf-var here-abst))))
          (env (bwf↓ here-abst wf-ℕ bwf[])
               (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
               (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here)))))

-- 4b. MIXED Θ (a reveal AND a conceal): the case a "restrict R2 to
-- boundaries with cmax = 0" design would NOT cover, and which IS reached
-- (it is exactly the shape R1 produces in §2).
--   redex:  ((λz:Z. z) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z→Z ⟫) · 3     :  ℕ
⊢redex-R2m : Δm ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3) ⦂ `ℕ
⊢redex-R2m =
  ⊢· (env (bwf↑ wf-ℕ (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
          (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
          (⊢ƛ (wf-var here-abst) (⊢` here)))
     ⊢$

_ : swapᵇ Θm 0 ≡ 2
_ = refl

⊢contractum-R2m :
  Δm ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) · (($ 3) ⟪ dualᵇ Θm , ` 2 ⟫)) ⟪ Θm , ` 0 ⟫ ⦂ `ℕ
⊢contractum-R2m =
  env (bwf↑ wf-ℕ (bwf↓ (skip-abst here-abst) wf-ℕ bwf[]))
      (sc-var hereᵒ)
      (⊢· (⊢ƛ (wf-var here-abst) (⊢` here))
          (env (bwf↑ wf-ℕ (bwf↑ wf-ℕ (bwf↓ here-abst wf-ℕ bwf[])))
               (sc-var (thereᵒ (thereᵒ hereᵒ)))
               ⊢$))

------------------------------------------------------------------------
-- 4c.  NESTED WRAPPERS AT AN ELIMINATION POSITION
--
-- R2 puts a wrapper around the ARGUMENT, so a wrapped argument becomes a
-- NESTED wrapper; after Beta it can end up at an elimination position.
-- `nest` below is exactly that (it is ⊢contractum-R2's argument, wrapped
-- by the enclosing boundary).  R1′ — which requires the body to be
-- syntactically  Λ V  — is STUCK on it, so the "direct combine" design
-- needs a merge rule; R1 (float inside) fires and turns it into the
-- §2 redex ⊢redex-R1.
------------------------------------------------------------------------

nest : Term
nest = (polyid ⟪ cnc 0 `ℕ ∷ [] , ∀ZZ ⟫) ⟪ Θr , ∀ZZ ⟫

⊢nest : [] ∣ [] ⊢ nest ⦂ ∀ZZ
⊢nest = env (bwf↑ wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (env (bwf↓ here-abst wf-ℕ bwf[])
                 (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
                 (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))

⊢nest-redex : [] ∣ [] ⊢ nest ·[ ` 0 ⇒ ` 0 , `𝔹 ] ⦂ (`𝔹 ⇒ `𝔹)
⊢nest-redex = ⊢·[] ⊢nest wf-𝔹

-- R1's contractum.  ⇑ᵀ of the inner wrapper bumps its conceal index 0 ↦ 1
-- and leaves the body alone (the conceal absorbs the shift: intRen suc
-- [cnc 0 ℕ] = id) — written out literally, since BReduction's renameᵀ is
-- not imported here.
⊢nest-R1 :
  [] ∣ [] ⊢ ((polyid ⟪ cnc 1 `ℕ ∷ [] , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ])
              ⟪ rvl `𝔹 ∷ shiftReps Θr , ` 0 ⇒ ` 0 ⟫
            ⦂ (`𝔹 ⇒ `𝔹)
⊢nest-R1 =
  env (bwf↑ wf-𝔹 (bwf↑ wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢·[] (env (bwf↓ (skip-abst here-abst) wf-ℕ bwf[])
                 (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
                 (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
            (wf-var here-abst))

-- and that contractum's inner redex is ⊢redex-R1's, at Δ8 = [Y , X]:
_ : (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    ≡ (polyid ⟪ cnc 1 `ℕ ∷ [] , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
_ = refl

------------------------------------------------------------------------
-- 5.  R3 (Drop) and R4 (Cancel), and the term that no sound rule can step
------------------------------------------------------------------------

-- R3.  Θ = [] makes both faces B₀ and the interior context the exterior,
-- so  V ⟪ [] , B₀ ⟫ -→ V  is type preserving.  (Proved for all B₀.)
γᵇ-[] : ∀ B → substᵗ (γᵇ []) B ≡ B
γᵇ-[] B = trans (subst-cong (λ X → refl) B) (subst-id B)

ρᵇ-[] : ∀ B → substᵗ (ρᵇ []) B ≡ B
ρᵇ-[] B = subst-id B

_ : [] ∣ [] ⊢ ($ 5) ⟪ [] , `ℕ ⟫ ⦂ `ℕ
_ = env bwf[] sc-ℕ ⊢$

_ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
_ = ⊢$

-- R4 (Cancel).  A conceal of the enclosing reveal's variable, with the
-- SAME rep, is the identity: both faces of the pair are `ℕ here.
_ : [] ∣ [] ⊢ (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl `ℕ ∷ [] , ` 0 ⟫ ⦂ `ℕ
_ = env (bwf↑ wf-ℕ bwf[]) (sc-var hereᵒ)
        (env (bwf↓ here-abst wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

_ : [] ∣ [] ⊢ $ 7 ⦂ `ℕ                    -- the Cancel contractum
_ = ⊢$

------------------------------------------------------------------------
-- 5a.  THE COUNTEREXAMPLE TO PROGRESS-FROM-TYPING-ALONE.
--
-- (env) has no premise relating a conceal's rep to the rep of the reveal
-- whose variable it conceals (by design — §2 records ONE boundary type
-- and derives both faces).  So the SAME variable can be concealed at ℕ
-- and revealed at ∀(Z→Z):  a closed VALUE of type ∀(Z→Z) whose entire
-- content is  $ 7.
------------------------------------------------------------------------

bad : Term
bad = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl ∀ZZ ∷ [] , ` 0 ⟫

⊢bad : [] ∣ [] ⊢ bad ⦂ ∀ZZ
⊢bad = env (bwf↑ (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst))) bwf[])
           (sc-var hereᵒ)
           (env (bwf↓ here-abst wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

-- `bad` is a value (V-⟪⟫ of a V-⟪⟫ of V-$), it is not a Λ, and its
-- boundary type is NOT ∀-shaped, so neither R1 nor R1′ applies:
bad-B₀-not-∀ : ¬ (Σ Ty λ T → (` 0) ≡ `∀ T)
bad-B₀-not-∀ (T , ())

-- so this closed, well-typed elimination is STUCK …
⊢bad-redex : [] ∣ [] ⊢ bad ·[ ` 0 ⇒ ` 0 , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢bad-redex = ⊢·[] ⊢bad wf-ℕ

-- … and R4 (Cancel) cannot rescue it: the reps disagree (ℕ vs ∀(Z→Z)),
-- and the cancel contractum $ 7 does not have the redex's type.
bad-cancel-ill-typed : ¬ ([] ∣ [] ⊢ $ 7 ⦂ ∀ZZ)
bad-cancel-ill-typed ()

-- The term is UNREACHABLE (no rule mints a conceal whose rep disagrees
-- with the enclosing reveal: R2's conceals come from dualᵇ, which copies
-- the reveal's own rep), so progress must be stated for the reachable
-- terms — or (env) must be tightened.  See the memo, §2 and §4.

------------------------------------------------------------------------
-- 6.  CANONICAL FORMS (PLAN §5)
--
-- Values are  V-$ | V-G (ƛ / Λ) | V-⟪⟫.  For an elimination to fire on a
-- closed value we must know which of these can carry a ⇒ / ∀ type, and —
-- for the wrapper case — the SHAPE of B₀, since that is what selects the
-- rule.  The two lemmas below are the shape analysis; they need only the
-- exterior face, not the derivation.
------------------------------------------------------------------------

cf-∀-B₀ : ∀ Θ B₀ {B} → substᵗ (ρᵇ Θ) B₀ ≡ `∀ B
  → (Σ Ty λ B₀′ → B₀ ≡ `∀ B₀′)
  ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))
cf-∀-B₀ Θ (` X) eq with split (revs Θ) X
cf-∀-B₀ Θ (` X) eq | inj₁ X<r        = inj₂ (X , refl , X<r)
cf-∀-B₀ Θ (` X) eq | inj₂ (i , refl) =
  ⊥-elim (var≢∀ (trans (sym (ρᵇ-hi Θ i)) eq))
  where
    var≢∀ : ∀ {j T} → (` j) ≡ `∀ T → ⊥
    var≢∀ ()
cf-∀-B₀ Θ `ℕ      ()
cf-∀-B₀ Θ `𝔹      ()
cf-∀-B₀ Θ (A ⇒ B) ()
cf-∀-B₀ Θ (`∀ T)  eq = inj₁ (T , refl)

cf-⇒-B₀ : ∀ Θ B₀ {A B} → substᵗ (ρᵇ Θ) B₀ ≡ (A ⇒ B)
  → (Σ Ty λ B₁ → Σ Ty λ B₂ → B₀ ≡ (B₁ ⇒ B₂))
  ⊎ (Σ ℕ λ X → (B₀ ≡ ` X) × (X < revs Θ))
cf-⇒-B₀ Θ (` X) eq with split (revs Θ) X
cf-⇒-B₀ Θ (` X) eq | inj₁ X<r        = inj₂ (X , refl , X<r)
cf-⇒-B₀ Θ (` X) eq | inj₂ (i , refl) =
  ⊥-elim (var≢⇒ (trans (sym (ρᵇ-hi Θ i)) eq))
  where
    var≢⇒ : ∀ {j S T} → (` j) ≡ (S ⇒ T) → ⊥
    var≢⇒ ()
cf-⇒-B₀ Θ `ℕ         ()
cf-⇒-B₀ Θ `𝔹         ()
cf-⇒-B₀ Θ (B₁ ⇒ B₂)  eq = inj₁ (B₁ , B₂ , refl)
cf-⇒-B₀ Θ (`∀ T)     ()

-- In the second alternative B₀ is a REVEAL variable, so by γᵇ-lo the
-- interior type of the body is the ABSTRACT variable ` X.  No $, ƛ or Λ
-- has a variable type, so the body must itself be a wrapper whose own
-- boundary type is a variable — and the chain can only stop at a CONCEAL
-- of that variable (γᵇ's only non-variable output).  That is precisely
-- the `bad`/Cancel configuration of §5a.  Stated as the lemmas progress
-- would use (proofs deferred; sanity-checked against the typing rules and
-- against the witnesses in §5–5a):
--
--   canon-⟪⟫-∀ : Value V → Δ ∣ [] ⊢ V ⟪ Θ , B₀ ⟫ ⦂ `∀ B
--              → (Σ Ty λ B₀′ → B₀ ≡ `∀ B₀′)          -- R1 fires
--              ⊎ (Σ ℕ λ X → B₀ ≡ ` X × X < revs Θ)   -- §5a, unreachable
--
--   canon-⟪⟫-⇒ : Value V → Δ ∣ [] ⊢ V ⟪ Θ , B₀ ⟫ ⦂ (A ⇒ B)
--              → (Σ Ty λ B₁ → Σ Ty λ B₂ → B₀ ≡ (B₁ ⇒ B₂))   -- R2 fires
--              ⊎ (Σ ℕ λ X → B₀ ≡ ` X × X < revs Θ)
--
--   canon-var  : Value V → Δ ∣ [] ⊢ V ⦂ ` X
--              → Σ Term λ V′ → Σ BCtx λ Θ → Σ ℕ λ Y →
--                  V ≡ V′ ⟪ Θ , ` Y ⟫
--
--   canon-∀    : Value V → [] ∣ [] ⊢ V ⦂ `∀ B
--              → (Σ Term λ V′ → V ≡ Λ V′)
--              ⊎ (Σ Term λ V′ → Σ BCtx λ Θ → Σ Ty λ B₀ →
--                   V ≡ V′ ⟪ Θ , B₀ ⟫)
--   canon-⇒, canon-ℕ : likewise.
--
-- With R1 and R2 in their "float inside" form (they do NOT require the
-- body to be a Λ / ƛ) the only progress obligation left is the second
-- alternative of canon-⟪⟫-∀ / canon-⟪⟫-⇒.
