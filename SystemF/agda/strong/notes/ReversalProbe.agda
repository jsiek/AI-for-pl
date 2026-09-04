module strong.notes.ReversalProbe where

-- DESIGN FEASIBILITY PROBE (not part of the development) for DECISIONS.md
-- Decision 3's CANDIDATE FIX: compare a conceal's representation with the
-- exterior's knowledge in the EXTERIOR ("reversal form"), instead of
-- transporting the knowledge into the interior (Decision 1's §5c form).
--
--   (bwf-↓ʳ)  Δ ∋ X := A₀      A[ρΘ] = ⇑^{X+1} A₀      Ψ ⊢ A
--             Δ ∣ Ψ ⊢ᵇʳ Θ  ⟹  Δ ∣ Ψ ⊢ᵇʳ (↓X:=A , Θ)
--
-- where A[ρΘ] is A (a type over the interior Ψ) READ BACK OUT through the
-- whole boundary: a reveal variable ↦ its rep (a Δ-type), a kept interior
-- variable ↦ its Δ-index.  That map is exactly MergeProbe's `outSub Θ`.
-- A₀ is Δ's knowledge, a type over the tail Δ ↓ X (strong.Context's ∋:= is
-- tail-relative), so it is lifted into Δ by ⇑^{suc X}; BOTH SIDES ARE
-- TYPES OVER Δ.  (Comparing in Δ ↓ X instead would need A[ρΘ] pushed down,
-- which is partial; Δ is where both readings already live.)
--
-- Contents
--   §0  intOfR (interior knowledge entries ⟦A⟧, Decision-1 refinement) and
--       the variant judgements _∣_⊢ᵇʳ_ / _∣_⊢ʳ_⦂_
--   §1  `bad` and `bad₂` are NOT typable under ⊢ʳ                        ✓
--   §2  Merge: `redexo` types AND the merged boundary types (the interior
--       form's `no-merge` obstruction is gone); ¬⊕-bwf's pair composes    ✓
--   §3  Example 8's trace T0 … T5 under ⊢ʳ                               ✓
--   §4  Wrap's dual: read-back through the dual = the interior reading    ✓
--   §5  the premise transports under renaming, NO scope restriction       ✓
--   §6  Decision 4 / W3 on the blocked-knowledge example                  ✓
--
-- Nothing here edits any other file.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (_≟_; m≤m+n; m+[n∸m]≡n; ≤-trans; ≤-refl; +-identityʳ; m≤m⊔n;
         m+n≮m; m+n∸m≡n; ≤⇒≯)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-cong; rename-rename-commute; rename-subst-commute;
         rename-subst)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         _∋_:=_; here; ∋:=→∋tv;
         Ctx; _∋_⦂_; there; ⤊)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; _-→_;
         TyBeta; Beta; TyWrap; Wrap; ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫;
         ⇑ᵀ; polyid; ∀ZZ;
         dualᵇ; swapᵇ; repOf; rvlsOf; cncOfRevs; shiftReps;
         revs-dual; cmax-dual; ρᵇ-dual-lo; γcnc-conc; γcnc-kept;
         isConc-<; acc-of; slotsᴳ-ok;
         Mono; Mono→≤; restrictRen; deepRen; intRen; renᴮ; liftⁿ;
         liftⁿ-lo; liftⁿ-hi; revs-ren; cmax-ren; CmaxV; cm-0; cm-s;
         split; ρᵇ-comm; prepId-hi)
open import strong.notes.GroundedProbe
  using (bad; bad₂; ⊢∀ZZ; sc∀ZZ; Bfun; body8; src;
         Θr; Θc; Θ8′; Θn; Θi; Δ1′; Δ8′;
         T0; T1; T2; T3; T4; T5; W2; W3; R1body; T5body; inner₂; mid₂;
         Δb; Θb; Δm′; Θm; liftRep; grounded)
open import strong.notes.MergeProbe
  using (outSub; sub-ren; _⊕_; Δo; Θ1o; Θ2o; Vo; redexo; Θold;
         Δbw; Θ1bw; Θ2bw)

private
  variable
    Δ Δ′ Ψ : TCtx
    Γₜ : Ctx
    A B C B₀ A₀ : Ty
    M N : Term
    Θ Ξ : BCtx
    x n X j : ℕ

------------------------------------------------------------------------
-- §0.  Interior knowledge entries, and the reversal judgements.
--
-- ⟦A⟧ (Decision 1's 2026-09-04 refinement): the INTERIOR READING of a
-- reveal's rep A — concealed exterior variables ↦ their conceal reps, kept
-- ones re-indexed — and `abst` (no knowledge) when A names a BLOCKED slot.
-- Since strong.Context reads a `rvld` entry as a type over its own TAIL,
-- the reading for the reveal at interior slot j is additionally shifted
-- down past the j reveals above it (`dnT (suc j)`).
------------------------------------------------------------------------

isOk : Slot → Bool
isOk ok  = true
isOk blk = false

-- bfree Θ d A : A (a Δ-type under d binders) names no BLOCKED slot of Θ
bfree : BCtx → ℕ → Ty → Bool
bfree Θ d (` X) with X <? d
... | yes _ = true
... | no  _ = isOk (slotAt Θ (X ∸ d))
bfree Θ d `ℕ      = true
bfree Θ d `𝔹      = true
bfree Θ d (A ⇒ B) = bfree Θ d A ∧ bfree Θ d B
bfree Θ d (`∀ A)  = bfree Θ (suc d) A

dnT : ℕ → Ty → Ty                     -- shift down past k entries
dnT k = renameᵗ (_∸ k)

-- rdRep Θ A : the interior reading of the Δ-type A, over the WHOLE interior
rdRep : BCtx → Ty → Ty
rdRep Θ A = substᵗ (γᵇ Θ) (renameᵗ (revs Θ +_) A)

⟦_⟧ᵉ : BCtx → ℕ → Ty → TyEntry        -- the entry of the reveal at slot j
⟦ Θ ⟧ᵉ j A = if bfree Θ 0 A then rvld (dnT (suc j) (rdRep Θ A)) else abst

revEntsR : BCtx → ℕ → BCtx → TCtx
revEntsR Θ j []            = []
revEntsR Θ j (rvl A   ∷ Ξ) = ⟦ Θ ⟧ᵉ j A ∷ revEntsR Θ (suc j) Ξ
revEntsR Θ j (cnc X A ∷ Ξ) = revEntsR Θ j Ξ

intOfR : TCtx → BCtx → TCtx
intOfR Δ Θ = revEntsR Θ 0 Θ ++ dropN (cmax Θ) Δ

-- same SHAPE as intOf, so γᵇ / ρᵇ / baseS are reusable unchanged
len-revEntsR : ∀ Θ j Ξ → length (revEntsR Θ j Ξ) ≡ revs Ξ
len-revEntsR Θ j []            = refl
len-revEntsR Θ j (rvl A   ∷ Ξ) = cong suc (len-revEntsR Θ (suc j) Ξ)
len-revEntsR Θ j (cnc X A ∷ Ξ) = len-revEntsR Θ j Ξ

------------------------------------------------------------------------
-- THE REVERSAL PREMISE
------------------------------------------------------------------------

outRead : BCtx → Ty → Ty              -- interior type ↦ exterior type
outRead Θ A = substᵗ (outSub Θ) A

upRep : ℕ → Ty → Ty                   -- (Δ ↓ X)-type ↦ Δ-type
upRep X A₀ = renameᵗ (λ i → suc X + i) A₀

Reversal : BCtx → ℕ → Ty → Ty → Set
Reversal Θ X A A₀ = outRead Θ A ≡ upRep X A₀

-- boundary well-formedness.  The premise mentions outSub of the WHOLE
-- boundary, so Θ is a parameter (as in DECISIONS §5c's note).
data Bwfʳ (Δ Ψ : TCtx) (Θ : BCtx) : BCtx → Set where
  bwf[]ʳ : Bwfʳ Δ Ψ Θ []
  bwf↑ʳ  : ∀ {A Ξ} → Δ ⊢ A → Bwfʳ Δ Ψ Θ Ξ → Bwfʳ Δ Ψ Θ (rvl A ∷ Ξ)
  bwf↓ʳ  : ∀ {X A A₀ Ξ}
         → Δ ∋ X := A₀ → Reversal Θ X A A₀ → Ψ ⊢ A
         → Bwfʳ Δ Ψ Θ Ξ → Bwfʳ Δ Ψ Θ (cnc X A ∷ Ξ)

infix 4 _∣_⊢ᵇʳ_
_∣_⊢ᵇʳ_ : TCtx → TCtx → BCtx → Set
Δ ∣ Ψ ⊢ᵇʳ Θ = Bwfʳ Δ Ψ Θ Θ

infix 3 _∣_⊢ʳ_⦂_
data _∣_⊢ʳ_⦂_ : TCtx → Ctx → Term → Ty → Set where
  ⊢`ʳ   : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢ʳ ` x ⦂ A
  ⊢$ʳ   : Δ ∣ Γₜ ⊢ʳ $ n ⦂ `ℕ
  ⊢ƛʳ   : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢ʳ N ⦂ B → Δ ∣ Γₜ ⊢ʳ ƛ A ∙ N ⦂ (A ⇒ B)
  ⊢·ʳ   : Δ ∣ Γₜ ⊢ʳ M ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢ʳ N ⦂ A → Δ ∣ Γₜ ⊢ʳ M · N ⦂ B
  ⊢Λʳ   : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢ʳ N ⦂ C → Δ ∣ Γₜ ⊢ʳ Λ N ⦂ `∀ C
  ⊢·[]ʳ : Δ ∣ Γₜ ⊢ʳ M ⦂ `∀ B → Δ ⊢ A → Δ ∣ Γₜ ⊢ʳ M ·[ B , A ] ⦂ B [ A ]ᵗ
  envʳ  : Δ ∣ intOfR Δ Θ ⊢ᵇʳ Θ
        → Scoped (baseS Θ Δ) B₀
        → intOfR Δ Θ ∣ [] ⊢ʳ M ⦂ substᵗ (γᵇ Θ) B₀
          ---------------------------------------------------
        → Δ ∣ Γₜ ⊢ʳ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- §1.  `bad` and `bad₂` are refuted.
--
--   bad  = ((7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫)
--   bad₂ = GroundedProbe §5's closed stuck value, which passes the naive
--          (untransported) interior premise.
------------------------------------------------------------------------

-- the outer boundary's interior: X REVEALED at ∀Z.Z→Z
_ : intOfR [] (rvl ∀ZZ ∷ []) ≡ rvld ∀ZZ ∷ []
_ = refl

-- reading ℕ back out of ↓X:=ℕ gives ℕ; the exterior knows ∀Z.Z→Z
¬⊢badʳ : ¬ ([] ∣ [] ⊢ʳ bad ⦂ ∀ZZ)
¬⊢badʳ (envʳ _ _ (envʳ (bwf↓ʳ here () _ _) _ _))

-- bad₂'s two outer reveals rebuild exactly GroundedProbe's Δb …
_ : intOfR (intOfR [] (rvl ∀ZZ ∷ [])) (rvl (` 0) ∷ []) ≡ Δb
_ = refl

-- … and there the reversal premise SEES the confusion the naive form missed:
-- ` 0 read back out of Θb is ℕ (the reveal Z's rep), while Δb's knowledge
-- about X, lifted, is ` 1 (the deeper P).
_ : outRead Θb (` 0) ≡ `ℕ
_ = refl

_ : upRep 0 (` 0) ≡ ` 1
_ = refl

¬Reversal-bad₂ : ¬ (Reversal Θb 0 (` 0) (` 0))
¬Reversal-bad₂ ()

¬⊢bad₂ʳ : ¬ ([] ∣ [] ⊢ʳ bad₂ ⦂ ∀ZZ)
¬⊢bad₂ʳ (envʳ _ _ (envʳ _ _ (envʳ (bwf↑ʳ _ (bwf↓ʳ here () _ _)) _ _)))

-- for contrast, GroundedProbe's §5c interior premise and the reversal
-- premise agree on the CLOSED-rep conceals (both accept) …
_ : grounded Θc 0 `ℕ `ℕ
_ = refl

_ : Reversal Θc 0 `ℕ `ℕ
_ = refl

-- … and both reject bad₂'s conceal, but for the dual reasons: `grounded`
-- transports the KNOWLEDGE inwards (` 0 ↦ ` 1), `Reversal` transports the
-- REP outwards (` 0 ↦ ℕ).
_ : substᵗ (γᵇ Θb) (liftRep Θb 0 (` 0)) ≡ ` 1
_ = refl

------------------------------------------------------------------------
-- §2.  Merge (Decision 3).  MergeProbe §4c's redex has NO well-typed
-- merged boundary under the interior premise (`no-merge`).  Under the
-- reversal premise it does: the conceal ↓X:=(W→W) is licensed because
-- (W→W)[ρΘ] = ℕ→ℕ = Δo's knowledge — the boundary's OWN reveal is
-- unfolded, which is exactly Zdancewic's Δ̄ / (trans).
--
--   Δo = [X := ℕ→ℕ]   Θ₂ = ↓X:=ℕ→ℕ   Θ₁ = ↑W:=ℕ   B₁ = W→W   B₂ = X
------------------------------------------------------------------------

_ : intOfR Δo Θ2o ≡ []
_ = refl

_ : intOfR [] Θ1o ≡ rvld `ℕ ∷ []
_ = refl

⊢redexoʳ : Δo ∣ [] ⊢ʳ redexo ⦂ ` 0
⊢redexoʳ =
  envʳ (bwf↓ʳ here refl (wf-⇒ wf-ℕ wf-ℕ) bwf[]ʳ) (sc-var hereᵒ)
       (envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
             (⊢ƛʳ (wf-var here-rvld) (⊢`ʳ here)))

-- NOTE (new).  MergeProbe's _⊕_ pushes Θ₂'s conceal rep INTO Ψ₁ through
-- `inSub Θ₁`, which for the closed rep ℕ→ℕ is the identity — so ⊕ produces
-- the UNFOLDED rep ℕ→ℕ, whose internal face is ℕ→ℕ, while V = λw:W.w has
-- type W→W in the interior.  The boundary Merge actually needs is Θold
-- (rep W→W): the two differ exactly by ONE UNFOLDING of the reveal W:=ℕ.
_ : Θ1o ⊕ Θ2o ≡ rvl `ℕ ∷ cnc 0 (`ℕ ⇒ `ℕ) ∷ []
_ = refl

_ : Θold ≡ rvl `ℕ ∷ cnc 0 (` 0 ⇒ ` 0) ∷ []
_ = refl

-- the ⊕-composite's internal face is ℕ→ℕ, not the body's type W→W …
_ : substᵗ (γᵇ (Θ1o ⊕ Θ2o)) (` 1) ≡ (`ℕ ⇒ `ℕ)
_ = refl

_ : intOfR Δo Θold ≡ rvld `ℕ ∷ []
_ = refl

-- the two faces of the merged wrapper: external ` 0 (= X), internal W→W
_ : substᵗ (ρᵇ Θold) (` 1) ≡ ` 0
_ = refl

_ : substᵗ (γᵇ Θold) (` 1) ≡ (` 0 ⇒ ` 0)
_ = refl

-- THE PAYOFF: the reversal premise ADMITS what the interior form refused.
Reversal-merged : Reversal Θold 0 (` 0 ⇒ ` 0) (`ℕ ⇒ `ℕ)
Reversal-merged = refl

⊢mergedoʳ : Δo ∣ [] ⊢ʳ Vo ⟪ Θold , ` 1 ⟫ ⦂ ` 0
⊢mergedoʳ =
  envʳ (bwf↑ʳ wf-ℕ
         (bwf↓ʳ here Reversal-merged
                (wf-⇒ (wf-var here-rvld) (wf-var here-rvld)) bwf[]ʳ))
       (sc-var (thereᵒ hereᵒ))
       (⊢ƛʳ (wf-var here-rvld) (⊢`ʳ here))

-- (for the record: the interior form pins the rep to ℕ→ℕ, so the SAME
-- boundary is rejected there — MergeProbe.¬⊢mergedo / no-merge.)
¬grounded-merged : ¬ (grounded Θold 0 (` 0 ⇒ ` 0) (`ℕ ⇒ `ℕ))
¬grounded-merged ()

------------------------------------------------------------------------
-- §2b.  MergeProbe §9's ¬⊕-bwf pair now COMPOSES.
--   Δ = [X:=P , P]   Θ₂ = ↓X:=P   Θ₁ = ↑W:=𝔹   Θ₁ ⊕ Θ₂ = ↑W:=𝔹 , ↓X:=P
------------------------------------------------------------------------

Ψ2bw Ψ1bw : TCtx
Ψ2bw = intOfR Δbw Θ2bw
Ψ1bw = intOfR Ψ2bw Θ1bw

_ : Ψ2bw ≡ abst ∷ []
_ = refl

_ : Ψ1bw ≡ rvld `𝔹 ∷ abst ∷ []
_ = refl

⊢Θ2bwʳ : Δbw ∣ Ψ2bw ⊢ᵇʳ Θ2bw
⊢Θ2bwʳ = bwf↓ʳ here refl (wf-var here-abst) bwf[]ʳ

⊢Θ1bwʳ : Ψ2bw ∣ Ψ1bw ⊢ᵇʳ Θ1bw
⊢Θ1bwʳ = bwf↑ʳ wf-𝔹 bwf[]ʳ

-- … and the composite, which GroundedProbe's untransported premise refuted:
⊕-bwfʳ : Δbw ∣ Ψ1bw ⊢ᵇʳ (Θ1bw ⊕ Θ2bw)
⊕-bwfʳ = bwf↑ʳ wf-𝔹
          (bwf↓ʳ here refl (wf-var (skip-rvld here-abst)) bwf[]ʳ)

------------------------------------------------------------------------
-- §3.  Example 8's trace, T0 … T5, under ⊢ʳ.
--
-- The interiors now agree with the ORIGINAL intOf wherever a reveal's rep
-- names a blocked slot: Θn = ↑Z:=Y , ↓X:=ℕ over Δ8′ = [Y , X:=ℕ] has Y
-- BLOCKED, so Z's entry is `abst` (no knowledge), and T5's inner boundary
-- re-reveals Z at its own slot.  The two conceals are ↓X:=ℕ at [X:=ℕ] and
-- at [Y , X:=ℕ]; both read back out to ℕ.
------------------------------------------------------------------------

_ : intOfR [] Θr ≡ Δ1′
_ = refl

_ : intOfR Δ1′ Θc ≡ []
_ = refl

_ : intOfR Δ8′ Θ8′ ≡ []
_ = refl

_ : intOfR Δ8′ Θn ≡ abst ∷ []                    -- Z abstract: its rep is Y
_ = refl

_ : intOfR (abst ∷ []) Θi ≡ rvld (` 0) ∷ abst ∷ []
_ = refl

⊢polyidʳ : ∀ {Δ Γₜ} → Δ ∣ Γₜ ⊢ʳ polyid ⦂ ∀ZZ
⊢polyidʳ = ⊢Λʳ (⊢ƛʳ (wf-var here-abst) (⊢`ʳ here))

⊢lam8ʳ : ∀ {Δ} → Δ ∣ [] ⊢ʳ (ƛ ∀ZZ ∙ body8) ⦂ Bfun
⊢lam8ʳ = ⊢ƛʳ ⊢∀ZZ (⊢Λʳ (⊢·[]ʳ (⊢`ʳ here) (wf-var here-abst)))

⊢T0ʳ : [] ∣ [] ⊢ʳ T0 ⦂ ∀ZZ
⊢T0ʳ = ⊢·ʳ (⊢·[]ʳ (⊢Λʳ ⊢lam8ʳ) wf-ℕ) ⊢polyidʳ

⊢T1ʳ : [] ∣ [] ⊢ʳ T1 ⦂ ∀ZZ
⊢T1ʳ = ⊢·ʳ (envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) (sc-⇒ sc∀ZZ sc∀ZZ) ⊢lam8ʳ) ⊢polyidʳ

⊢W2ʳ : Δ1′ ∣ [] ⊢ʳ W2 ⦂ ∀ZZ
⊢W2ʳ = envʳ (bwf↓ʳ here refl wf-ℕ bwf[]ʳ) sc∀ZZ ⊢polyidʳ

⊢T2ʳ : [] ∣ [] ⊢ʳ T2 ⦂ ∀ZZ
⊢T2ʳ = envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) sc∀ZZ (⊢·ʳ ⊢lam8ʳ ⊢W2ʳ)

⊢redexʳ : Δ8′ ∣ [] ⊢ʳ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ]) ⦂ (` 0 ⇒ ` 0)
⊢redexʳ = ⊢·[]ʳ (envʳ (bwf↓ʳ (skip-abst here) refl wf-ℕ bwf[]ʳ) sc∀ZZ ⊢polyidʳ)
                (wf-var here-abst)

⊢T3ʳ : [] ∣ [] ⊢ʳ T3 ⦂ ∀ZZ
⊢T3ʳ = envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) sc∀ZZ (⊢Λʳ ⊢redexʳ)

⊢Θnʳ : Δ8′ ∣ intOfR Δ8′ Θn ⊢ᵇʳ Θn
⊢Θnʳ = bwf↑ʳ (wf-var here-abst)
        (bwf↓ʳ (skip-abst here) refl wf-ℕ bwf[]ʳ)

⊢R1bodyʳ : Δ8′ ∣ [] ⊢ʳ R1body ⦂ (` 0 ⇒ ` 0)
⊢R1bodyʳ =
  envʳ ⊢Θnʳ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (⊢·[]ʳ ⊢polyidʳ (wf-var here-abst))

⊢T4ʳ : [] ∣ [] ⊢ʳ T4 ⦂ ∀ZZ
⊢T4ʳ = envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) sc∀ZZ (⊢Λʳ ⊢R1bodyʳ)

⊢innerʳ : (abst ∷ []) ∣ [] ⊢ʳ (ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫ ⦂ (` 0 ⇒ ` 0)
⊢innerʳ = envʳ (bwf↑ʳ (wf-var here-abst) bwf[]ʳ)
               (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
               (⊢ƛʳ (wf-var here-rvld) (⊢`ʳ here))

⊢T5bodyʳ : Δ8′ ∣ [] ⊢ʳ T5body ⦂ (` 0 ⇒ ` 0)
⊢T5bodyʳ = envʳ ⊢Θnʳ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)) ⊢innerʳ

⊢T5ʳ : [] ∣ [] ⊢ʳ T5 ⦂ ∀ZZ
⊢T5ʳ = envʳ (bwf↑ʳ wf-ℕ bwf[]ʳ) sc∀ZZ (⊢Λʳ ⊢T5bodyʳ)

-- every step is a real -→ (unchanged from GroundedProbe §2)
_ : T0 -→ T1
_ = ξ-·-l (TyBeta (V-G G-ƛ))
_ : T1 -→ T2
_ = Wrap (V-G G-ƛ) (V-G (G-Λ (V-G G-ƛ)))
_ : T2 -→ T3
_ = ξ-⟪⟫ (Beta (V-⟪⟫ (V-G (G-Λ (V-G G-ƛ)))))
_ : T3 -→ T4
_ = ξ-⟪⟫ (ξ-Λ (TyWrap (V-G (G-Λ (V-G G-ƛ)))))
_ : T4 -→ T5
_ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (TyBeta (V-G G-ƛ))))

------------------------------------------------------------------------
-- §4.  Wrap's dual.
--
-- Θᵈ = dualᵇ Θ has exterior Ψ = intOfR Δ Θ and conceals each reveal
-- variable j of Θ at its own rep A = ρᵇ Θ j (a Δ-type = a Θᵈ-interior
-- type).  The reversal premise asks: A READ BACK OUT through Θᵈ = Ψ's
-- knowledge about j, which is ⟦A⟧.  The read-back half is a THEOREM.
------------------------------------------------------------------------

outSub-lo : ∀ Θ X → X < revs Θ → outSub Θ X ≡ ρᵇ Θ X
outSub-lo Θ X lt with X <? revs Θ
... | yes _  = refl
... | no ¬lt = ⊥-elim (¬lt lt)

outSub-hi : ∀ Θ X → ¬ (X < revs Θ)
          → outSub Θ X ≡ ` (cmax Θ + (X ∸ revs Θ))
outSub-hi Θ X ¬lt with X <? revs Θ
... | yes lt = ⊥-elim (¬lt lt)
... | no  _  = refl

-- the dual's read-back map IS the interior reading map, at every
-- non-blocked slot (at a blocked slot the dual invents a dummy rep, which
-- is why (env)'s Scoped premise exists).
outSub-dual : ∀ Θ X → slotAt Θ X ≡ ok
            → outSub (dualᵇ Θ) X ≡ γcnc (revs Θ) (cmax Θ) Θ X
outSub-dual Θ X e with acc-of Θ X e
outSub-dual Θ X e | inj₁ le =
  trans (outSub-hi (dualᵇ Θ) X
          (λ lt → ≤⇒≯ le (subst (X <_) (revs-dual Θ) lt)))
        (trans (cong₂ (λ a b → ` (a + (X ∸ b))) (cmax-dual Θ) (revs-dual Θ))
               (sym (γcnc-kept (revs Θ) (cmax Θ) Θ X le)))
outSub-dual Θ X e | inj₂ c =
  trans (outSub-lo (dualᵇ Θ) X
          (subst (X <_) (sym (revs-dual Θ)) (isConc-< Θ X c)))
        (trans (ρᵇ-dual-lo Θ X (isConc-< Θ X c))
               (sym (γcnc-conc (revs Θ) (cmax Θ) Θ X c)))

rdRep-γcnc : ∀ Θ A → rdRep Θ A ≡ substᵗ (γcnc (revs Θ) (cmax Θ) Θ) A
rdRep-γcnc Θ A =
  trans (rename-subst-commute (revs Θ +_) (γᵇ Θ) A)
        (subst-cong (λ X → prepId-hi (revs Θ)
                            (γcnc (revs Θ) (cmax Θ) Θ) X) A)

-- THE GENERAL STATEMENT (read-back half), no side condition beyond the
-- one (env) already imposes on every type it looks at: A names no blocked
-- slot of Θ.
dual-read-back : ∀ {Δ : TCtx} Θ A → Scoped (slotsᴳ Θ 0 Δ) A
               → outRead (dualᵇ Θ) A ≡ rdRep Θ A
dual-read-back {Δ} Θ A sc =
  trans (subst-cong-sc sc
          (λ X okp → outSub-dual Θ X (slotsᴳ-ok Θ Δ 0 X okp)))
        (sym (rdRep-γcnc Θ A))

-- … and hence the dual's conceal of reveal j meets the premise exactly
-- when the telescope down-shift of the entry round-trips.
dual-cnc-Reversal : ∀ {Δ : TCtx} Θ j A
  → Scoped (slotsᴳ Θ 0 Δ) A
  → upRep j (dnT (suc j) (rdRep Θ A)) ≡ rdRep Θ A
  → Reversal (dualᵇ Θ) j A (dnT (suc j) (rdRep Θ A))
dual-cnc-Reversal Θ j A sc rt = trans (dual-read-back Θ A sc) (sym rt)

------------------------------------------------------------------------
-- §4a.  The mixed Wrap example (BReduction's Θm / GroundedProbe's Δm′).
--   Δm′ = [Y , X:=ℕ]   Θm = ↑Z:=ℕ , ↓X:=ℕ   Ψ = [Z:=ℕ]
------------------------------------------------------------------------

Ψm : TCtx
Ψm = intOfR Δm′ Θm

_ : Ψm ≡ rvld `ℕ ∷ []
_ = refl

_ : dualᵇ Θm ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

⊢Θmʳ : Δm′ ∣ Ψm ⊢ᵇʳ Θm
⊢Θmʳ = bwf↑ʳ wf-ℕ (bwf↓ʳ (skip-abst here) refl wf-ℕ bwf[]ʳ)

-- the dual is well formed: its conceal ↓Z:=ℕ reads back to ℕ = Ψm's
-- knowledge about Z.
⊢dualΘmʳ : Ψm ∣ intOfR Ψm (dualᵇ Θm) ⊢ᵇʳ dualᵇ Θm
⊢dualΘmʳ = bwf↑ʳ wf-ℕ (bwf↑ʳ wf-ℕ (bwf↓ʳ here refl wf-ℕ bwf[]ʳ))

_ : intOfR Ψm (dualᵇ Θm) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

-- the round-trip hypothesis of dual-cnc-Reversal, on this example
_ : upRep 0 (dnT 1 (rdRep Θm (ρᵇ Θm 0))) ≡ rdRep Θm (ρᵇ Θm 0)
_ = refl

------------------------------------------------------------------------
-- §4b.  NEW COUNTEREXAMPLE.  The dual is NOT always well formed: if a
-- reveal's rep names a BLOCKED slot, the Decision-1 refinement makes its
-- interior entry `abst` (no knowledge), and the dual's conceal of that
-- reveal variable then has nothing to point at.  Example 8's own Θn is
-- such a boundary (↑Z:=Y with Y blocked), and it is a RUN-TIME boundary
-- (T4/T5), so Wrap can reach it.  This is a consequence of the refinement,
-- not of the reversal form: the interior (§5c) premise fails identically.
------------------------------------------------------------------------

_ : dualᵇ Θn ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
_ = refl

_ : intOfR Δ8′ Θn ≡ abst ∷ []
_ = refl

¬knows-Z : ¬ (Σ Ty λ A₀ → (abst ∷ []) ∋ 0 := A₀)
¬knows-Z (A₀ , ())

¬⊢dualΘnʳ : ∀ {Ψ} → ¬ ((abst ∷ []) ∣ Ψ ⊢ᵇʳ dualᵇ Θn)
¬⊢dualΘnʳ (bwf↑ʳ _ (bwf↑ʳ _ (bwf↓ʳ () _ _ _)))

------------------------------------------------------------------------
-- §5.  Renaming transport — the point of the reversal form.
--
-- ⊢renameᵀ sends  cnc X A  to  cnc (ρ X) (renameᵗ (intRen ρ Θ) A)  and the
-- exterior knowledge  Δ ∋ X := A₀  to  Δ′ ∋ ρ X := renameᵗ (restrictRen X ρ) A₀.
-- The reversal premise transports along that with NO scope restriction:
-- the external face ρᵇ commutes with renaming everywhere (ρᵇ-comm), unlike
-- γᵇ, whose commutation needs Scoped (the interior form's `¬hk-int`).
------------------------------------------------------------------------

-- read-back commutes with renaming, pointwise, at EVERY interior index
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

-- the whole premise, transported
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

-- instance: GroundedProbe's ¬hk-int witness — Γ = [X:=ℕ , W],
-- Θ = ↑Z:=W , ↓X:=ℕ, weakened by a new abstract V at index 0.  The
-- interior form's entry moves; the reversal premise transports on the nose.
Γhk : TCtx
Γhk = rvld `ℕ ∷ abst ∷ []

Θhk : BCtx
Θhk = rvl (` 1) ∷ cnc 0 `ℕ ∷ []

_ : Reversal Θhk 0 `ℕ `ℕ
_ = refl

_ : renᴮ suc (intRen suc Θhk) Θhk ≡ rvl (` 2) ∷ cnc 1 `ℕ ∷ []
_ = refl

Mono-suc : Mono suc
Mono-suc lt = s≤s lt

_ : Reversal (renᴮ suc (intRen suc Θhk) Θhk) 1 `ℕ `ℕ
_ = Reversal-ren Mono-suc Θhk 0 `ℕ `ℕ refl

------------------------------------------------------------------------
-- §6.  Decision 4 and option (W3).
--
--   Δw = [Y:=𝔹 , X:=ℕ]   (both REVEALED; Y shallower)
--   h  = (λx:ℕ.x) ⟪ ↓X:=ℕ , X→X ⟫          Y BLOCKED, and it carries 𝔹
--   h′ = (λx:ℕ.x) ⟪ ↓Y:=𝔹 , ↓X:=ℕ , X→X ⟫  (W3: conceal Y too)
--   Wd = (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=𝔹 , X ⟫   the argument that uses Y's knowledge
------------------------------------------------------------------------

Δw : TCtx
Δw = rvld `𝔹 ∷ rvld `ℕ ∷ []

Θh Θh′ : BCtx
Θh  = cnc 1 `ℕ ∷ []                       -- h  : Y is blocked
Θh′ = cnc 0 `𝔹 ∷ cnc 1 `ℕ ∷ []            -- h′ : Y concealed with its knowledge

Wd : Term
Wd = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ cnc 0 `𝔹 ∷ [] , ` 1 ⟫

⊢Wd : Δw ∣ [] ⊢ʳ Wd ⦂ ` 1
⊢Wd = envʳ (bwf↓ʳ here refl wf-𝔹 bwf[]ʳ)
           (sc-var (thereᵒ hereᵒ))
           (envʳ (bwf↓ʳ here refl wf-ℕ bwf[]ʳ) (sc-var hereᵒ) ⊢$ʳ)

-- (a) h′ types under ⊢ʳ; both conceals read back to Δw's knowledge.
_ : intOfR Δw Θh′ ≡ []
_ = refl

_ : baseS Θh′ Δw ≡ ok ∷ ok ∷ []                -- nothing blocked any more
_ = refl

⊢h′ : Δw ∣ [] ⊢ʳ (ƛ `ℕ ∙ ` 0) ⟪ Θh′ , ` 1 ⇒ ` 1 ⟫ ⦂ (` 1 ⇒ ` 1)
⊢h′ = envʳ (bwf↓ʳ here refl wf-𝔹 (bwf↓ʳ (skip-rvld here) refl wf-ℕ bwf[]ʳ))
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
           (⊢ƛʳ wf-ℕ (⊢`ʳ here))

-- (b) h′'s dual rebuilds Δw ON THE NOSE …
_ : dualᵇ Θh′ ≡ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

dual-int-h′ : intOfR (intOfR Δw Θh′) (dualᵇ Θh′) ≡ Δw
dual-int-h′ = refl

-- … so Wd retypes there, and Wrap's contractum is well typed.
⊢Wd-in-dual : intOfR (intOfR Δw Θh′) (dualᵇ Θh′) ∣ [] ⊢ʳ Wd ⦂ ` 1
⊢Wd-in-dual = ⊢Wd

⊢R′ : Δw ∣ [] ⊢ʳ ((ƛ `ℕ ∙ ` 0) ⟪ Θh′ , ` 1 ⇒ ` 1 ⟫) · Wd ⦂ ` 1
⊢R′ = ⊢·ʳ ⊢h′ ⊢Wd

-- (c) and WITHOUT W3 the example really does break: h types, but its dual
-- gives the blocked slot Y the DUMMY rep ℕ, and Wd no longer retypes.
⊢h : Δw ∣ [] ⊢ʳ (ƛ `ℕ ∙ ` 0) ⟪ Θh , ` 1 ⇒ ` 1 ⟫ ⦂ (` 1 ⇒ ` 1)
⊢h = envʳ (bwf↓ʳ (skip-rvld here) refl wf-ℕ bwf[]ʳ)
          (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
          (⊢ƛʳ wf-ℕ (⊢`ʳ here))

_ : baseS Θh Δw ≡ blk ∷ ok ∷ []                -- Y blocked, but REVEALED
_ = refl

_ : dualᵇ Θh ≡ rvl `ℕ ∷ rvl `ℕ ∷ []            -- dummy rep ℕ at the blocked Y
_ = refl

_ : intOfR (intOfR Δw Θh) (dualᵇ Θh) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

¬⊢Wd-in-dual : ¬ ((rvld `ℕ ∷ rvld `ℕ ∷ []) ∣ [] ⊢ʳ Wd ⦂ ` 1)
¬⊢Wd-in-dual (envʳ (bwf↓ʳ here () _ _) _ _)

------------------------------------------------------------------------
-- §6a.  What W3 asks of TyWrap's contractum (STATED, not proved):
--
--   instead of  ⇑ᵀ V,  weaken V by "↑Z:=A, and in EVERY boundary of V that
--   has a conceal, insert the conceal  ↓Z:=⟦A⟧  of the new revealed slot",
--   where ⟦A⟧ = rdRep Θ (the knowledge, lifted into the boundary's exterior).
--
-- The inserted conceal's reversal premise is then exactly the ROUND TRIP
-- "read in, then read back out, is the identity" — Zdancewic's Δ̄ closure
-- in one step.  (Under the interior form it was instead automatic but
-- unusable, since the merged rep could not be unfolded; cf. §2.)
------------------------------------------------------------------------

W3-insert : ∀ Θ Y A₀
  → outRead Θ (rdRep Θ (upRep Y A₀)) ≡ upRep Y A₀
  → Reversal Θ Y (rdRep Θ (upRep Y A₀)) A₀
W3-insert Θ Y A₀ rt = rt

-- on the example: the inserted conceal is ↓Y:=𝔹 and the round trip holds
_ : rdRep Θh′ (upRep 0 `𝔹) ≡ `𝔹
_ = refl

_ : Reversal Θh′ 0 `𝔹 `𝔹
_ = W3-insert Θh′ 0 `𝔹 refl
