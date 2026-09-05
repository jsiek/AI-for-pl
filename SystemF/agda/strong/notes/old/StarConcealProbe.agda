module strong.notes.old.StarConcealProbe where

-- SUPERSEDED 2026-09-04 by the dual-conceal licence install
-- (notes/DualLicenseDesign.md): the rep-less conceal is live in
-- strong.Boundary, the dual emits it for a rep-LESS reveal
-- (strong.BReduction's cncOfRevs), and its licensing is proven in
-- strong.DualDef.

-- ADVERSARIAL PROBE of the REP-LESS CONCEAL  ↓Z:⋆  (constructor cnc⋆), the
-- mirror of today's rep-less reveal rvl⋆ (notes/DECISIONS.md, R2 / DualCnc,
-- and the "(a″) PROBE VERDICT — SURVIVED" block).
--
-- WHY.  (a″) + the hybrid entry ⟦·⟧ᴴ closes DualCnc everywhere except the
-- Λ-BOUND blocked reveal (UpToProbe's ¬DualCnc≈ᴴ-E8), and that residue was
-- to be closed by a VACUITY lemma (no-abstract-value): "the failing Wrap
-- needs a value at an abstract variable's type, and there is none".  The
-- supervisor's example E★ shows the vacuity argument is INSUFFICIENT — E★
-- reaches the very same Λ-bound DualCnc failure with an argument of type ℕ,
-- about which no-abstract-value says nothing.  §1 machine-checks E★; §2
-- installs cnc⋆ locally; §3 re-runs E★ through the fix (it works); §4 hunts
-- for what the fix breaks; §5 states the completed DualCnc case split and
-- relocates the vacuity lemma; §6 does renaming/retag; §7 exhibits E★′, a
-- NEW counterexample showing cnc⋆ is NOT SUFFICIENT (the same program with
-- the ∀-body mentioning its own variable is stuck in both regimes, and
-- vacuity is silent there too); §8 is the verdict.
--
-- METHOD (the choice the mandate asks me to declare): the live files are
-- UNTOUCHED.  cnc⋆ cannot be simulated inside today's BEntry — the fix needs
-- an entry that COUNTS in cmax (so it must be a conceal) yet is BLK in baseS
-- (so it must not be `isConc`), and today's `cnc X A` is `ok` at its slot by
-- construction.  Encoding it as `cnc X <dummy>` would hand B₀ permission to
-- name the slot and give it the dummy as its internal face — which is
-- literally `bad` (§4.0).  So §2 defines a LOCAL FOUR-CONSTRUCTOR BEntry★
-- and a parametrised copy of the boundary machinery, the boundary
-- well-formedness, the typing judgement, the ambient dual and the three
-- reduction rules E★ uses.  The star world is (a″) throughout: hybrid
-- interior entries and the conceal premise up to UpToProbe's ≈.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties using (_≟_; ≤⇒≯; +-identityʳ; +-suc; m≤m+n)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; Dec; yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import strong.Types
open import strong.TypeSubst using (subst-id; subst-cong; sub-sub)
open import strong.Context hiding (Δ; Γ; A; B; C; X; Y; Z; x; E)
open import strong.Weakening using (wf-rename-fv)
open import strong.Boundary
open import strong.BReduction
  using (repOf; entAt; copyRep; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ;
         swapᵇ; swapIdx; shiftReps; liftⁿ; deepRen; restrictRen; intRen;
         renᴮ; extⁿ; Mono; split; ent-here; ent-skip;
         ok≢blk; ∋ok-head; ∋ok-tail; ∋ok-≡; if-acc;
         _≼_; ≼[]; ≼abst; ≼rvld; ≼-refl;
         GVal; Value; G-ƛ; G-Λ; V-$; V-G; V-⟪⟫;
         _⊢_-→_; TyBeta; Beta; TyWrap; Wrap;
         ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫)
open import strong.DualDef using (DualRep; DualCnc; DualInt)
open import strong.notes.old.UnfoldProbe
  using (unfSub; unfoldᵉ; ∋:=-entAt; rvld≢abst; suc-inj; len-++;
         ∋tv-len; ⊢-len; baseS-len)
open import strong.notes.old.UpToProbe
  using (_≈Δ̄[_]_; ≈unf; ≈-refl; ≈-sym; ≈-trans; ≡→≈; ≈-⇒; ≈-∀;
         Reversal≈; Reversal→≈; ⟦_∣_⟧ᴴ; revEntsᴴ; intOfᴴ;
         Bwf≈; bwf≈[]; bwf≈↑; bwf≈⋆; bwf≈↓; _∣_⊢ᵇ≈_; bwf→bwf≈;
         _∣_⊢≈_⦂_; ⊢`≈; ⊢$≈; ⊢ƛ≈; ⊢·≈; ⊢Λ≈; ⊢·[]≈; env≈;
         unfEnt; entᴳ≈; rvlsᴳ≈; dualᴳ≈;
         _≼≈_; ≼≈[]; ≼≈abst; ≼≈rvld; ≼≈-refl; ≼→≼≈; ≼≈-len; ≼≈-∋:=;
         DualRep≈; DualCnc≈; DualInt≈; cnc-needs-knowledge;
         val-var-wrapper; Γq; Γq′; Θq; DualInt≈-Γq)

private
  variable
    Γ Δ Δ' Ψ Ψ' : TCtx
    Γₜ : Ctx
    A B C B₀ A₀ : Ty
    L M N : Term
    Θ Ξ : BCtx
    i j k n x X : ℕ

------------------------------------------------------------------------
-- §1.  E★, THE SUPERVISOR'S COUNTEREXAMPLE TO THE VACUITY ARGUMENT.
--
--   E★ = (ΛX. λf:(∀Z. ℕ→ℕ). ΛY. (f [Y]) 5) [ℕ] · (ΛZ. λn:ℕ. n)  : ∀Y. ℕ
--
-- The essential move is Pn's (instantiate an imported polymorphic value at
-- an ABSTRACT variable, f [Y]) with one change: the instantiated ∀-body does
-- NOT mention its own variable, so the argument the failing Wrap must move
-- inward has type ℕ, not Y.  Every step below is checked: each Tᵢ typed by
-- the live judgement, each step a live `_⊢_-→_`.
------------------------------------------------------------------------

polyf : Ty                     -- ∀Z. ℕ→ℕ   (Z UNUSED — that is the point)
polyf = `∀ (`ℕ ⇒ `ℕ)

Bprog : Ty                     -- the ∀-body TyBeta records
Bprog = polyf ⇒ `∀ `ℕ

body★ : Term                   -- the ΛY body:  (f [Y]) 5
body★ = ((` 0) ·[ `ℕ ⇒ `ℕ , ` 0 ]) · ($ 5)

fn★ : Term                     -- λf:(∀Z.ℕ→ℕ). ΛY. (f [Y]) 5
fn★ = ƛ polyf ∙ (Λ body★)

id★ : Term                     -- ΛZ. λn:ℕ. n
id★ = Λ (ƛ `ℕ ∙ (` 0))

T0 : Term
T0 = ((Λ fn★) ·[ Bprog , `ℕ ]) · id★

Θ1 : BCtx                      -- ↑X:=ℕ, the boundary TyBeta is born with
Θ1 = rvl `ℕ ∷ []

T1 : Term
T1 = (fn★ ⟪ Θ1 , Bprog ⟫) · id★

Θd : BCtx                      -- dualᴳ [] Θ1 = ↓X:=ℕ   (X at index 0)
Θd = cnc 0 `ℕ ∷ []

_ : dualᴳ [] Θ1 ≡ Θd
_ = refl

-- CORRECTION 1 to the memo's trace: passing under the ΛY renames the dual's
-- conceal INDEX (substᵀᵐ's Λ clause applies ⇑ᵀ, whose wrapper clause is
-- renᴮ suc), so the boundary written ↓X:=ℕ at T2 carries index 1, not 0.
Θd′ : BCtx
Θd′ = cnc 1 `ℕ ∷ []

T2 : Term
T2 = (Λ (((id★ ⟪ Θd′ , polyf ⟫) ·[ `ℕ ⇒ `ℕ , ` 0 ]) · ($ 5)))
     ⟪ Θ1 , `∀ `ℕ ⟫

Γ★ : TCtx                      -- Y (Λ-bound, 0) , X:=ℕ (1)  — Boundary's Γ₈
Γ★ = abst ∷ rvld `ℕ ∷ []

_ : Γ★ ≡ Γ₈
_ = refl

Θ★ : BCtx                      -- ↑Z:=Y , ↓X:=ℕ, minted by TyWrap at Γ★
Θ★ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []

T3 : Term
T3 = (Λ ((((ƛ `ℕ ∙ (` 0)) ⟪ Θ★ , `ℕ ⇒ `ℕ ⟫) · ($ 5)))) ⟪ Θ1 , `∀ `ℕ ⟫

-- the live dual at the failing step: ↑Y:⋆ (Y is Λ-bound, so REP-LESS),
-- ↑X:=ℕ (copied from Θ★'s conceal rep), ↓Z:=Y (the unlicensable one)
dualᵛ : BCtx
dualᵛ = rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ Γ★ Θ★ ≡ dualᵛ
_ = refl

_ : dualᴳ≈ Γ★ Θ★ ≡ dualᵛ       -- (a″) changes nothing here: no chained rep
_ = refl

T4 : Term                      -- the contractum, under Λ, inside ⟪Θ1⟫
T4 = (($ 5) ⟪ dualᵛ , `ℕ ⟫) ⟪ Θ★ , `ℕ ⟫

T4full : Term
T4full = (Λ T4) ⟪ Θ1 , `∀ `ℕ ⟫

------------------------------------------------------------------------
-- §1.1  The four steps, by the LIVE reduction relation.
------------------------------------------------------------------------

step01 : [] ⊢ T0 -→ T1
step01 = ξ-·-l (TyBeta (V-G G-ƛ))

step12 : [] ⊢ T1 -→ T2
step12 = Wrap (V-G (G-Λ (V-G G-ƛ)))

step23 : [] ⊢ T2 -→ T3
step23 = ξ-⟪⟫ (ξ-Λ (ξ-·-l (TyWrap (V-G G-ƛ))))

step34 : [] ⊢ T3 -→ T4full
step34 = ξ-⟪⟫ (ξ-Λ (Wrap V-$))

-- and T4's Wrap is FORCED: at T3 the only redex is that application (its
-- function is a wrapped ƛ, its argument is a value, and no other position
-- is reducible), so no evaluation order avoids the failure.
_ : Value ($ 5)
_ = V-$

------------------------------------------------------------------------
-- §1.2  T0 … T3 all type.  (Program type ∀Y.ℕ = `∀ `ℕ.)
------------------------------------------------------------------------

wf-polyf : ∀ {Δ₁ : TCtx} → Δ₁ ⊢ polyf
wf-polyf = wf-∀ (wf-⇒ wf-ℕ wf-ℕ)

sc-polyf : ∀ {Ψ₁ : SCtx} → Scoped Ψ₁ polyf
sc-polyf = sc-∀ (sc-⇒ sc-ℕ sc-ℕ)

⊢fn★ : ∀ {Δ₁ : TCtx} → Δ₁ ∣ [] ⊢ fn★ ⦂ Bprog
⊢fn★ = ⊢ƛ wf-polyf (⊢Λ (⊢· (⊢·[] (⊢` here) (wf-var here-abst)) ⊢$))

⊢id★ : ∀ {Δ₁ : TCtx} {Γ₁ : Ctx} → Δ₁ ∣ Γ₁ ⊢ id★ ⦂ polyf
⊢id★ = ⊢Λ (⊢ƛ wf-ℕ (⊢` here))

⊢T0 : [] ∣ [] ⊢ T0 ⦂ `∀ `ℕ
⊢T0 = ⊢· (⊢·[] (⊢Λ ⊢fn★) wf-ℕ) ⊢id★

⊢T1 : [] ∣ [] ⊢ T1 ⦂ `∀ `ℕ
⊢T1 = ⊢· (env (bwf↑ wf-ℕ bwf[])
              (sc-⇒ sc-polyf (sc-∀ sc-ℕ)) ⊢fn★) ⊢id★

-- the dual-wrapped argument, under the ΛY (so at Γ★, conceal index 1)
⊢argᵛ : Γ★ ∣ Γₜ ⊢ id★ ⟪ Θd′ , polyf ⟫ ⦂ polyf
⊢argᵛ = env (bwf↓ (skip-abst here) refl wf-ℕ bwf[]) sc-polyf ⊢id★

⊢T2 : [] ∣ [] ⊢ T2 ⦂ `∀ `ℕ
⊢T2 = env (bwf↑ wf-ℕ bwf[]) (sc-∀ sc-ℕ)
          (⊢Λ (⊢· (⊢·[] ⊢argᵛ (wf-var here-abst)) ⊢$))

bwf-Θ★ : Γ★ ∣ intOf Γ★ Θ★ ⊢ᵇ Θ★
bwf-Θ★ = bwf↑ (wf-var here-abst) (bwf↓ (skip-abst here) refl wf-ℕ bwf[])

_ : intOf Γ★ Θ★ ≡ abst ∷ []          -- Z's entry is ABSTRACT: "Z is Y" is
_ = refl                             -- not expressible where Y is blocked

_ : intOfᴴ Γ★ Θ★ ≡ abst ∷ []         -- and the HYBRID cannot help: unfoldᵉ
_ = refl                             -- is the identity at an abstract Y

⊢T3 : [] ∣ [] ⊢ T3 ⦂ `∀ `ℕ
⊢T3 = env (bwf↑ wf-ℕ bwf[]) (sc-∀ sc-ℕ)
          (⊢Λ (⊢· (env bwf-Θ★ (sc-⇒ sc-ℕ sc-ℕ) (⊢ƛ wf-ℕ (⊢` here))) ⊢$))

------------------------------------------------------------------------
-- §1.3  THE FAILURE AT T4, three ways.  The dual must conceal Z, whose
-- interior entry is abstract: bwf↓'s FIRST premise is a knowledge LOOKUP,
-- which neither ≈ nor the hybrid can supply.
------------------------------------------------------------------------

¬⊢T4 : ¬ (Γ★ ∣ [] ⊢ T4 ⦂ `ℕ)
¬⊢T4 (env _ _ (env (bwf⋆ (bwf↑ _ (bwf↓ () _ _ _))) _ _))

¬⊢T4≈ : ¬ (Γ★ ∣ [] ⊢≈ T4 ⦂ `ℕ)
¬⊢T4≈ (env≈ _ _ (env≈ (bwf≈⋆ (bwf≈↑ _ (bwf≈↓ () _ _ _))) _ _))

-- the DualCnc-shaped statement, instantiated on E★'s own Θ★ / Γ★ (the shape
-- of UpToProbe's ¬DualCnc≈ᴴ-E8, now reached by a CLOSED PROGRAM)
¬DualCnc-E★ :
  ¬ (Σ Ty λ A₀ → (intOf Γ★ Θ★ ∋ 0 := A₀)
               × Reversal dualᵛ 0 (ρᵇ Θ★ 0) A₀)
¬DualCnc-E★ (A₀ , () , _)

¬DualCnc≈ᴴ-E★ :
  ¬ (Σ Ty λ A₀ → (intOfᴴ Γ★ Θ★ ∋ 0 := A₀)
               × Reversal≈ (intOfᴴ Γ★ Θ★) dualᵛ 0 (ρᵇ Θ★ 0) A₀)
¬DualCnc≈ᴴ-E★ (A₀ , () , _)

-- WHY VACUITY DOES NOT REACH IT.  no-abstract-value's hypothesis is a value
-- at a VARIABLE type; E★'s Wrap argument is `$ 5` at `ℕ.  The two are
-- disjoint, so the lemma is silent here — the residue is NOT vacuous.
arg-type-E★ : Γ★ ∣ [] ⊢ $ 5 ⦂ `ℕ
arg-type-E★ = ⊢$

vacuity-silent : ¬ (`ℕ ≡ ` X)
vacuity-silent ()

-- (and the interior entry really is abstract, so cnc-needs-knowledge fires
-- in the direction that KILLS the conceal, not the one that saves the step)
entAt-Z-abst : entAt (intOfᴴ Γ★ Θ★) 0 ≡ abst
entAt-Z-abst = refl

no-Z-knowledge : ∀ {A₁} → intOfᴴ Γ★ Θ★ ∋ 0 := A₁ → ⊥
no-Z-knowledge p = cnc-needs-knowledge p entAt-Z-abst

------------------------------------------------------------------------
-- §2.  THE FIX: A REP-LESS CONCEAL  ↓Z:⋆  (cnc⋆), mirror of rvl⋆.
--
-- Semantics, entry by entry (the mandate's specification, made definitional):
--   cmax★    : cnc⋆ X COUNTS — the slot is dropped, exactly as ↓X:=A drops it
--   γcnc★    : NO image — the slot is not `isConc`, so γᵇ★ never resolves it
--   isConc★  : cnc⋆ contributes NOTHING, hence slotAt★ marks the slot `blk`
--              and (env★)'s Scoped premise forbids B₀ from naming it
--   ρᵇ★      : unchanged (conceals never touch the exterior face)
--   revEnts★ : contributes no interior entry (it is a conceal)
--   bwf★⋆↓   : the ONLY premise is  Γ ∋tv X  — it asserts no knowledge, so
--              it needs none
--   renᴮ★    : renames the INDEX only (there is no rep to rename)
-- The dual emits cnc⋆ j for a reveal at interior slot j whose knowledge is
-- inexpressible AND un-unfoldable — precisely the ⟦·⟧ᴴ-abstract case.
--
-- The star world is (a″): interiors use the HYBRID entry and the conceal
-- premise is up to UpToProbe's ≈.
------------------------------------------------------------------------

data BEntry★ : Set where
  rvl★  : Ty → BEntry★       -- ↑X:=A
  rvl⋆★ : BEntry★            -- ↑X:⋆   (today's rvl⋆)
  cnc★  : ℕ → Ty → BEntry★   -- ↓X:=A
  cnc⋆  : ℕ → BEntry★        -- ↓X:⋆   *** THE FIX ***

BCtx★ : Set
BCtx★ = List BEntry★

revs★ : BCtx★ → ℕ
revs★ []              = 0
revs★ (rvl★ A ∷ Ξ)    = suc (revs★ Ξ)
revs★ (rvl⋆★ ∷ Ξ)     = suc (revs★ Ξ)
revs★ (cnc★ X A ∷ Ξ)  = revs★ Ξ
revs★ (cnc⋆ X ∷ Ξ)    = revs★ Ξ

cmax★ : BCtx★ → ℕ                  -- cnc⋆ COUNTS, exactly like cnc
cmax★ []              = 0
cmax★ (rvl★ A ∷ Ξ)    = cmax★ Ξ
cmax★ (rvl⋆★ ∷ Ξ)     = cmax★ Ξ
cmax★ (cnc★ X A ∷ Ξ)  = suc X ⊔ cmax★ Ξ
cmax★ (cnc⋆ X ∷ Ξ)    = suc X ⊔ cmax★ Ξ

ρᵇ★ : BCtx★ → Substᵗ               -- cnc⋆ leaves the exterior face alone
ρᵇ★ []              = `_
ρᵇ★ (rvl★ A ∷ Ξ)    = A •ᵗ ρᵇ★ Ξ
ρᵇ★ (rvl⋆★ ∷ Ξ)     = `ℕ •ᵗ ρᵇ★ Ξ
ρᵇ★ (cnc★ X A ∷ Ξ)  = ρᵇ★ Ξ
ρᵇ★ (cnc⋆ X ∷ Ξ)    = ρᵇ★ Ξ

γcnc★ : ℕ → ℕ → BCtx★ → Substᵗ     -- cnc⋆ has NO γ-image
γcnc★ r m []              = λ i → ` (r + (i ∸ m))
γcnc★ r m (rvl★ A ∷ Ξ)    = γcnc★ r m Ξ
γcnc★ r m (rvl⋆★ ∷ Ξ)     = γcnc★ r m Ξ
γcnc★ r m (cnc★ X A ∷ Ξ)  = sover X A (γcnc★ r m Ξ)
γcnc★ r m (cnc⋆ X ∷ Ξ)    = γcnc★ r m Ξ

γᵇ★ : BCtx★ → Substᵗ
γᵇ★ Ξ = prepId (revs★ Ξ) (γcnc★ (revs★ Ξ) (cmax★ Ξ) Ξ)

isConc★ : ℕ → BCtx★ → Bool         -- cnc⋆ is NOT a conceal for the scope
isConc★ i []              = false  -- test — that is what makes it `blk`
isConc★ i (rvl★ A ∷ Ξ)    = isConc★ i Ξ
isConc★ i (rvl⋆★ ∷ Ξ)     = isConc★ i Ξ
isConc★ i (cnc★ X A ∷ Ξ)  = ⌊ i ≟ X ⌋ ∨ isConc★ i Ξ
isConc★ i (cnc⋆ X ∷ Ξ)    = isConc★ i Ξ

slotAt★ : BCtx★ → ℕ → Slot
slotAt★ Ξ i with cmax★ Ξ ≤? i
slotAt★ Ξ i | yes _ = ok
slotAt★ Ξ i | no  _ = if isConc★ i Ξ then ok else blk

slotsᴳ★ : BCtx★ → ℕ → TCtx → SCtx
slotsᴳ★ Ξ i []      = []
slotsᴳ★ Ξ i (_ ∷ Γ) = slotAt★ Ξ i ∷ slotsᴳ★ Ξ (suc i) Γ

revSlots★ : BCtx★ → SCtx
revSlots★ []              = []
revSlots★ (rvl★ A ∷ Ξ)    = ok ∷ revSlots★ Ξ
revSlots★ (rvl⋆★ ∷ Ξ)     = blk ∷ revSlots★ Ξ
revSlots★ (cnc★ X A ∷ Ξ)  = revSlots★ Ξ
revSlots★ (cnc⋆ X ∷ Ξ)    = revSlots★ Ξ

baseS★ : BCtx★ → TCtx → SCtx
baseS★ Ξ Γ = revSlots★ Ξ ++ slotsᴳ★ Ξ 0 Γ

bfree★ : BCtx★ → ℕ → Ty → Bool
bfree★ Ξ d (` X)   = ⌊ X <? d ⌋ ∨ isOk (slotAt★ Ξ (X ∸ d))
bfree★ Ξ d `ℕ      = true
bfree★ Ξ d `𝔹      = true
bfree★ Ξ d (A ⇒ B) = bfree★ Ξ d A ∧ bfree★ Ξ d B
bfree★ Ξ d (`∀ A)  = bfree★ Ξ (suc d) A

rdSub★ : BCtx★ → Substᵗ
rdSub★ Ξ = γcnc★ (revs★ Ξ) (cmax★ Ξ) Ξ

rawRead★ : BCtx★ → Ty → Ty
rawRead★ Ξ A = substᵗ (rdSub★ Ξ) A

⟦_⟧ᵉ★ : BCtx★ → ℕ → Ty → TyEntry
⟦ Ξ ⟧ᵉ★ j A =
  if bfree★ Ξ 0 A ∧ dfree 0 (suc j) (rawRead★ Ξ A)
  then rvld (dnT (suc j) (rawRead★ Ξ A))
  else abst

-- the HYBRID entry (a″): raw where expressible, retried at the ambient
-- unfolding where not, abstract only when both fail
⟦_∣_⟧ᴴ★ : TCtx → BCtx★ → ℕ → Ty → TyEntry
⟦ Γ ∣ Ξ ⟧ᴴ★ j A = hyb (⟦ Ξ ⟧ᵉ★ j A)
  where
    hyb : TyEntry → TyEntry
    hyb (rvld B) = rvld B
    hyb abst     = ⟦ Ξ ⟧ᵉ★ j (unfoldᵉ Γ A)

revEnts★ : TCtx → BCtx★ → ℕ → BCtx★ → TCtx
revEnts★ Γ Ξ j []              = []
revEnts★ Γ Ξ j (rvl★ A ∷ Ζ)    = ⟦ Γ ∣ Ξ ⟧ᴴ★ j A ∷ revEnts★ Γ Ξ (suc j) Ζ
revEnts★ Γ Ξ j (rvl⋆★ ∷ Ζ)     = abst ∷ revEnts★ Γ Ξ (suc j) Ζ
revEnts★ Γ Ξ j (cnc★ X A ∷ Ζ)  = revEnts★ Γ Ξ j Ζ
revEnts★ Γ Ξ j (cnc⋆ X ∷ Ζ)    = revEnts★ Γ Ξ j Ζ

intOf★ : TCtx → BCtx★ → TCtx
intOf★ Γ Ξ = revEnts★ Γ Ξ 0 Ξ ++ dropN (cmax★ Ξ) Γ

outSub★ : BCtx★ → Substᵗ
outSub★ Ξ X with X <? revs★ Ξ
outSub★ Ξ X | yes _ = ρᵇ★ Ξ X
outSub★ Ξ X | no  _ = ` (cmax★ Ξ + (X ∸ revs★ Ξ))

outRead★ : BCtx★ → Ty → Ty
outRead★ Ξ A = substᵗ (outSub★ Ξ) A

Reversal★ : TCtx → BCtx★ → ℕ → Ty → Ty → Set
Reversal★ Γ Ξ X A A₀ = outRead★ Ξ A ≈Δ̄[ Γ ] upRep X A₀

------------------------------------------------------------------------
-- Boundary well-formedness, with the ONE new rule: cnc⋆ asks only that the
-- slot exists.
------------------------------------------------------------------------

data Bwf★ (Γ Ψ : TCtx) (Ξ : BCtx★) : BCtx★ → Set where
  bwf★[] : Bwf★ Γ Ψ Ξ []
  bwf★↑  : ∀ {A Ζ} → Γ ⊢ A → Bwf★ Γ Ψ Ξ Ζ → Bwf★ Γ Ψ Ξ (rvl★ A ∷ Ζ)
  bwf★⋆  : ∀ {Ζ} → Bwf★ Γ Ψ Ξ Ζ → Bwf★ Γ Ψ Ξ (rvl⋆★ ∷ Ζ)
  bwf★↓  : ∀ {X A A₀ Ζ}
         → Γ ∋ X := A₀ → Reversal★ Γ Ξ X A A₀ → Ψ ⊢ A
         → Bwf★ Γ Ψ Ξ Ζ → Bwf★ Γ Ψ Ξ (cnc★ X A ∷ Ζ)
  bwf★⋆↓ : ∀ {X Ζ}                       -- *** THE FIX'S RULE ***
         → Γ ∋tv X → Bwf★ Γ Ψ Ξ Ζ → Bwf★ Γ Ψ Ξ (cnc⋆ X ∷ Ζ)

infix 4 _∣_⊢ᵇ★_
_∣_⊢ᵇ★_ : TCtx → TCtx → BCtx★ → Set
Γ ∣ Ψ ⊢ᵇ★ Ξ = Bwf★ Γ Ψ Ξ Ξ

------------------------------------------------------------------------
-- Terms and typing (a parametrised copy; only (env★) differs from today's
-- rules, and only in that it reads the star boundary).
------------------------------------------------------------------------

infix  9 `★_
infix  9 $★_
infixl 7 _·★_
infix  6 ƛ★_∙_
infix  5 _⟪_,_⟫★

data Term★ : Set where
  `★_      : ℕ → Term★
  $★_      : ℕ → Term★
  ƛ★_∙_    : Ty → Term★ → Term★
  _·★_     : Term★ → Term★ → Term★
  Λ★_      : Term★ → Term★
  _·★[_,_] : Term★ → Ty → Ty → Term★
  _⟪_,_⟫★  : Term★ → BCtx★ → Ty → Term★

private
  variable
    Ξ⋆ Ζ⋆ : BCtx★
    K★ L★ M★ N★ V★ W★ L★′ M★′ N★′ : Term★

infix 3 _∣_⊢★_⦂_
data _∣_⊢★_⦂_ : TCtx → Ctx → Term★ → Ty → Set where
  ⊢★`   : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢★ `★ x ⦂ A
  ⊢★$   : Δ ∣ Γₜ ⊢★ $★ n ⦂ `ℕ
  ⊢★ƛ   : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢★ N★ ⦂ B → Δ ∣ Γₜ ⊢★ ƛ★ A ∙ N★ ⦂ (A ⇒ B)
  ⊢★·   : Δ ∣ Γₜ ⊢★ L★ ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢★ M★ ⦂ A
        → Δ ∣ Γₜ ⊢★ L★ ·★ M★ ⦂ B
  ⊢★Λ   : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢★ N★ ⦂ C → Δ ∣ Γₜ ⊢★ Λ★ N★ ⦂ `∀ C
  ⊢★·[] : Δ ∣ Γₜ ⊢★ L★ ⦂ `∀ B → Δ ⊢ A
        → Δ ∣ Γₜ ⊢★ L★ ·★[ B , A ] ⦂ B [ A ]ᵗ
  env★  : Δ ∣ intOf★ Δ Ξ⋆ ⊢ᵇ★ Ξ⋆
        → Scoped (baseS★ Ξ⋆ Δ) B₀
        → intOf★ Δ Ξ⋆ ∣ [] ⊢★ M★ ⦂ substᵗ (γᵇ★ Ξ⋆) B₀
          ---------------------------------------------------
        → Δ ∣ Γₜ ⊢★ M★ ⟪ Ξ⋆ , B₀ ⟫★ ⦂ substᵗ (ρᵇ★ Ξ⋆) B₀

data GVal★ : Term★ → Set
data Value★ : Term★ → Set

data GVal★ where
  G★-ƛ : GVal★ (ƛ★ A ∙ N★)
  G★-Λ : Value★ V★ → GVal★ (Λ★ V★)

data Value★ where
  V★-$  : Value★ ($★ n)
  V★-G  : GVal★ V★ → Value★ V★
  V★-⟪⟫ : Value★ V★ → Value★ (V★ ⟪ Ξ⋆ , B₀ ⟫★)

------------------------------------------------------------------------
-- The ambient dual.  Its reveal block is (a″)'s entᴳ≈ verbatim; its
-- CONCEAL block is where cnc⋆ enters: a reveal whose interior entry is
-- knowledge is concealed at that knowledge (as today), and a reveal whose
-- entry is ABSTRACT — inexpressible raw AND un-unfoldable — is RE-HIDDEN
-- with cnc⋆, asserting nothing.  rvl⋆ (which had no rep to begin with) goes
-- the same way; today it gets the bogus `cnc j `ℕ`, which is unlicensable
-- for the same reason (§4.3).
------------------------------------------------------------------------

repOf★ : ℕ → BCtx★ → Ty
repOf★ i []              = `ℕ
repOf★ i (rvl★ A ∷ Ξ)    = repOf★ i Ξ
repOf★ i (rvl⋆★ ∷ Ξ)     = repOf★ i Ξ
repOf★ i (cnc⋆ X ∷ Ξ)    = repOf★ i Ξ
repOf★ i (cnc★ X A ∷ Ξ) with i ≟ X
repOf★ i (cnc★ X A ∷ Ξ) | yes _ = A
repOf★ i (cnc★ X A ∷ Ξ) | no  _ = repOf★ i Ξ

entᴳ★ : TCtx → BCtx★ → ℕ → ℕ → BEntry★
entᴳ★ Γ Ξ i k with isConc★ i Ξ
entᴳ★ Γ Ξ i k | true  = rvl★ (repOf★ i Ξ)
entᴳ★ Γ Ξ i k | false with entAt Γ i
entᴳ★ Γ Ξ i k | false | abst   = rvl⋆★
entᴳ★ Γ Ξ i k | false | rvld B with dfree 0 k B
entᴳ★ Γ Ξ i k | false | rvld B | true  =
  rvl★ (copyRep k (revs★ Ξ) B)
entᴳ★ Γ Ξ i k | false | rvld B | false with dfree 0 k (unfEnt Γ i B)
entᴳ★ Γ Ξ i k | false | rvld B | false | true  =
  rvl★ (copyRep k (revs★ Ξ) (unfEnt Γ i B))
entᴳ★ Γ Ξ i k | false | rvld B | false | false = rvl⋆★

rvlsᴳ★ : ℕ → ℕ → TCtx → BCtx★ → BCtx★
rvlsᴳ★ zero    s Γ Ξ = []
rvlsᴳ★ (suc k) s Γ Ξ = entᴳ★ Γ Ξ s k ∷ rvlsᴳ★ k (suc s) Γ Ξ

cncOfRevs★ : TCtx → BCtx★ → ℕ → BCtx★ → BCtx★
cncOfRevs★ Γ Ξ j []              = []
cncOfRevs★ Γ Ξ j (rvl⋆★ ∷ Ζ)     = cnc⋆ j ∷ cncOfRevs★ Γ Ξ (suc j) Ζ
cncOfRevs★ Γ Ξ j (cnc★ X A ∷ Ζ)  = cncOfRevs★ Γ Ξ j Ζ
cncOfRevs★ Γ Ξ j (cnc⋆ X ∷ Ζ)    = cncOfRevs★ Γ Ξ j Ζ
cncOfRevs★ Γ Ξ j (rvl★ A ∷ Ζ) with ⟦ Γ ∣ Ξ ⟧ᴴ★ j A
cncOfRevs★ Γ Ξ j (rvl★ A ∷ Ζ) | rvld B =
  cnc★ j A ∷ cncOfRevs★ Γ Ξ (suc j) Ζ
cncOfRevs★ Γ Ξ j (rvl★ A ∷ Ζ) | abst   =
  cnc⋆ j ∷ cncOfRevs★ Γ Ξ (suc j) Ζ

dualᴳ★ : TCtx → BCtx★ → BCtx★
dualᴳ★ Γ Ξ = rvlsᴳ★ (cmax★ Ξ) 0 Γ Ξ ++ cncOfRevs★ Γ Ξ 0 Ξ

swapᵇ★ : BCtx★ → ℕ → ℕ
swapᵇ★ Ξ = swapIdx (revs★ Ξ) (cmax★ Ξ)

------------------------------------------------------------------------
-- Renaming and term substitution (needed to state the Wrap rule; cnc⋆
-- renames its INDEX only).
------------------------------------------------------------------------

renᴮ★ : (ℕ → ℕ) → (ℕ → ℕ) → BCtx★ → BCtx★
renᴮ★ ρ ir []              = []
renᴮ★ ρ ir (rvl★ A ∷ Ξ)    = rvl★ (renameᵗ ρ A) ∷ renᴮ★ ρ ir Ξ
renᴮ★ ρ ir (rvl⋆★ ∷ Ξ)     = rvl⋆★ ∷ renᴮ★ ρ ir Ξ
renᴮ★ ρ ir (cnc★ X A ∷ Ξ)  = cnc★ (ρ X) (renameᵗ ir A) ∷ renᴮ★ ρ ir Ξ
renᴮ★ ρ ir (cnc⋆ X ∷ Ξ)    = cnc⋆ (ρ X) ∷ renᴮ★ ρ ir Ξ

intRen★ : (ℕ → ℕ) → BCtx★ → (ℕ → ℕ)
intRen★ ρ Ξ = liftⁿ (revs★ Ξ) (deepRen (cmax★ Ξ) ρ)

renameᵀ★ : (ℕ → ℕ) → Term★ → Term★
renameᵀ★ ρ (`★ x)          = `★ x
renameᵀ★ ρ ($★ n)          = $★ n
renameᵀ★ ρ (ƛ★ A ∙ N★)     = ƛ★ (renameᵗ ρ A) ∙ renameᵀ★ ρ N★
renameᵀ★ ρ (L★ ·★ M★)      = renameᵀ★ ρ L★ ·★ renameᵀ★ ρ M★
renameᵀ★ ρ (Λ★ N★)         = Λ★ (renameᵀ★ (extᵗ ρ) N★)
renameᵀ★ ρ (L★ ·★[ B , A ]) =
  renameᵀ★ ρ L★ ·★[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renameᵀ★ ρ (M★ ⟪ Ξ⋆ , B₀ ⟫★) =
  renameᵀ★ (intRen★ ρ Ξ⋆) M★
  ⟪ renᴮ★ ρ (intRen★ ρ Ξ⋆) Ξ⋆ , renameᵗ (liftⁿ (revs★ Ξ⋆) ρ) B₀ ⟫★

⇑ᵀ★ : Term★ → Term★
⇑ᵀ★ = renameᵀ★ suc

renameᵀᵐ★ : (ℕ → ℕ) → Term★ → Term★
renameᵀᵐ★ ρ (`★ x)           = `★ (ρ x)
renameᵀᵐ★ ρ ($★ n)           = $★ n
renameᵀᵐ★ ρ (ƛ★ A ∙ N★)      = ƛ★ A ∙ renameᵀᵐ★ (extⁿ ρ) N★
renameᵀᵐ★ ρ (L★ ·★ M★)       = renameᵀᵐ★ ρ L★ ·★ renameᵀᵐ★ ρ M★
renameᵀᵐ★ ρ (Λ★ N★)          = Λ★ (renameᵀᵐ★ ρ N★)
renameᵀᵐ★ ρ (L★ ·★[ B , A ]) = renameᵀᵐ★ ρ L★ ·★[ B , A ]
renameᵀᵐ★ ρ (M★ ⟪ Ξ⋆ , B₀ ⟫★) = M★ ⟪ Ξ⋆ , B₀ ⟫★

extsᵀᵐ★ : (ℕ → Term★) → (ℕ → Term★)
extsᵀᵐ★ σ zero    = `★ zero
extsᵀᵐ★ σ (suc x) = renameᵀᵐ★ suc (σ x)

substᵀᵐ★ : (ℕ → Term★) → Term★ → Term★
substᵀᵐ★ σ (`★ x)           = σ x
substᵀᵐ★ σ ($★ n)           = $★ n
substᵀᵐ★ σ (ƛ★ A ∙ N★)      = ƛ★ A ∙ substᵀᵐ★ (extsᵀᵐ★ σ) N★
substᵀᵐ★ σ (L★ ·★ M★)       = substᵀᵐ★ σ L★ ·★ substᵀᵐ★ σ M★
substᵀᵐ★ σ (Λ★ N★)          = Λ★ (substᵀᵐ★ (λ x → ⇑ᵀ★ (σ x)) N★)
substᵀᵐ★ σ (L★ ·★[ B , A ]) = substᵀᵐ★ σ L★ ·★[ B , A ]
substᵀᵐ★ σ (M★ ⟪ Ξ⋆ , B₀ ⟫★) = M★ ⟪ Ξ⋆ , B₀ ⟫★

infix 8 _[_]ᵐ★
_[_]ᵐ★ : Term★ → Term★ → Term★
N★ [ W★ ]ᵐ★ = substᵀᵐ★ (λ { zero → W★ ; (suc x) → `★ x }) N★

------------------------------------------------------------------------
-- The three reduction rules E★'s failing step needs, verbatim from the
-- live relation with dualᴳ ↦ dualᴳ★.
------------------------------------------------------------------------

infix 2 _⊢★_-→★_
data _⊢★_-→★_ : TCtx → Term★ → Term★ → Set where
  Wrap★  : ∀ {A′ B₁ B₂} → Value★ W★
         → Δ ⊢★ ((ƛ★ A′ ∙ N★) ⟪ Ξ⋆ , B₁ ⇒ B₂ ⟫★) ·★ W★
           -→★ (N★ [ W★ ⟪ dualᴳ★ Δ Ξ⋆
                        , renameᵗ (swapᵇ★ Ξ⋆) B₁ ⟫★ ]ᵐ★) ⟪ Ξ⋆ , B₂ ⟫★
  ξ★-·-l : Δ ⊢★ L★ -→★ L★′ → Δ ⊢★ L★ ·★ M★ -→★ L★′ ·★ M★
  ξ★-Λ   : (abst ∷ Δ) ⊢★ N★ -→★ N★′ → Δ ⊢★ Λ★ N★ -→★ Λ★ N★′
  ξ★-⟪⟫  : intOf★ Δ Ξ⋆ ⊢★ M★ -→★ M★′
         → Δ ⊢★ M★ ⟪ Ξ⋆ , B₀ ⟫★ -→★ M★′ ⟪ Ξ⋆ , B₀ ⟫★

------------------------------------------------------------------------
-- §2.1  FAITHFULNESS OF THE COPY.  The star world extends the live one:
-- embedding a live boundary changes nothing that the live design computes.
------------------------------------------------------------------------

emb : BCtx → BCtx★
emb []            = []
emb (rvl A ∷ Θ₁)  = rvl★ A ∷ emb Θ₁
emb (rvl⋆ ∷ Θ₁)   = rvl⋆★ ∷ emb Θ₁
emb (cnc X A ∷ Θ₁) = cnc★ X A ∷ emb Θ₁

revs-emb : ∀ Θ₁ → revs★ (emb Θ₁) ≡ revs Θ₁
revs-emb []             = refl
revs-emb (rvl A ∷ Θ₁)   = cong suc (revs-emb Θ₁)
revs-emb (rvl⋆ ∷ Θ₁)    = cong suc (revs-emb Θ₁)
revs-emb (cnc X A ∷ Θ₁) = revs-emb Θ₁

cmax-emb : ∀ Θ₁ → cmax★ (emb Θ₁) ≡ cmax Θ₁
cmax-emb []             = refl
cmax-emb (rvl A ∷ Θ₁)   = cmax-emb Θ₁
cmax-emb (rvl⋆ ∷ Θ₁)    = cmax-emb Θ₁
cmax-emb (cnc X A ∷ Θ₁) = cong (suc X ⊔_) (cmax-emb Θ₁)

isConc-emb : ∀ i Θ₁ → isConc★ i (emb Θ₁) ≡ isConc i Θ₁
isConc-emb i []             = refl
isConc-emb i (rvl A ∷ Θ₁)   = isConc-emb i Θ₁
isConc-emb i (rvl⋆ ∷ Θ₁)    = isConc-emb i Θ₁
isConc-emb i (cnc X A ∷ Θ₁) = cong (⌊ i ≟ X ⌋ ∨_) (isConc-emb i Θ₁)

ρᵇ-emb : ∀ Θ₁ X → ρᵇ★ (emb Θ₁) X ≡ ρᵇ Θ₁ X
ρᵇ-emb []             X       = refl
ρᵇ-emb (rvl A ∷ Θ₁)   zero    = refl
ρᵇ-emb (rvl A ∷ Θ₁)   (suc X) = ρᵇ-emb Θ₁ X
ρᵇ-emb (rvl⋆ ∷ Θ₁)    zero    = refl
ρᵇ-emb (rvl⋆ ∷ Θ₁)    (suc X) = ρᵇ-emb Θ₁ X
ρᵇ-emb (cnc X A ∷ Θ₁) Y       = ρᵇ-emb Θ₁ Y

revSlots-emb : ∀ Θ₁ → revSlots★ (emb Θ₁) ≡ revSlots Θ₁
revSlots-emb []             = refl
revSlots-emb (rvl A ∷ Θ₁)   = cong (ok ∷_) (revSlots-emb Θ₁)
revSlots-emb (rvl⋆ ∷ Θ₁)    = cong (blk ∷_) (revSlots-emb Θ₁)
revSlots-emb (cnc X A ∷ Θ₁) = revSlots-emb Θ₁

-- and on E★'s own boundaries the interiors and both faces are IDENTICAL to
-- the live (a″) ones, entry for entry
_ : intOf★ Γ★ (emb Θ★) ≡ intOfᴴ Γ★ Θ★
_ = refl

_ : intOf★ Γ★ (emb Θd′) ≡ intOfᴴ Γ★ Θd′
_ = refl

_ : intOf★ [] (emb Θ1) ≡ intOfᴴ [] Θ1
_ = refl

_ : dualᴳ★ Γ★ (emb Θd′) ≡ emb (dualᴳ≈ Γ★ Θd′)
_ = refl

------------------------------------------------------------------------
-- §3.  E★ AFTER THE FIX.  The trace up to T3 is UNCHANGED (the fix touches
-- only the dual's conceal block), so §3 picks up at T3's image and runs the
-- failing Wrap through the star world.
------------------------------------------------------------------------

embT : Term → Term★
embT (` x)          = `★ x
embT ($ n)          = $★ n
embT (ƛ A ∙ N)      = ƛ★ A ∙ embT N
embT (L · M)        = embT L ·★ embT M
embT (Λ N)          = Λ★ (embT N)
embT (L ·[ B , A ]) = embT L ·★[ B , A ]
embT (M ⟪ Θ , B₀ ⟫) = embT M ⟪ emb Θ , B₀ ⟫★

Θ1★ Θ★ˢ : BCtx★
Θ1★ = emb Θ1                   -- ↑X:=ℕ
Θ★ˢ = emb Θ★                   -- ↑Z:=Y , ↓X:=ℕ

-- *** THE FIXED DUAL ***  ↑Y:⋆ , ↑X:=ℕ , ↓Z:⋆ — the third entry is the one
-- that changes: the dual RE-HIDES the reveal whose knowledge ("Z is Y") is
-- inexpressible in an interior that dropped Y, claiming nothing about it.
dual⋆ : BCtx★
dual⋆ = rvl⋆★ ∷ rvl★ `ℕ ∷ cnc⋆ 0 ∷ []

_ : dualᴳ★ Γ★ Θ★ˢ ≡ dual⋆
_ = refl

-- CORRECTION 2 to the memo's trace: the dual's entries come out in the order
-- [reveals for the dropped Γ-slots][conceals of the reveals], i.e.
-- ↑Y:⋆ , ↑X:=ℕ , ↓Z:⋆ — not ↓Z:⋆ , ↑Y:⋆ , ↑X:=ℕ.  (ρᵇ/γᵇ read the list
-- positionally, so the order is not cosmetic.)

T3★ T4★ T4full★ : Term★
T3★ = embT T3
T4★ = (($★ 5) ⟪ dual⋆ , `ℕ ⟫★) ⟪ Θ★ˢ , `ℕ ⟫★
T4full★ = (Λ★ T4★) ⟪ Θ1★ , `∀ `ℕ ⟫★

-- T3★ really is T3's image (the live trace hands the star world this term)
_ : T3★ ≡ (Λ★ ((((ƛ★ `ℕ ∙ (`★ 0)) ⟪ Θ★ˢ , `ℕ ⇒ `ℕ ⟫★) ·★ ($★ 5))))
          ⟪ Θ1★ , `∀ `ℕ ⟫★
_ = refl

step34★ : [] ⊢★ T3★ -→★ T4full★
step34★ = ξ★-⟪⟫ (ξ★-Λ (Wrap★ V★-$))

------------------------------------------------------------------------
-- §3.1  Both sides of the step type, at the program's type ∀Y.ℕ.
------------------------------------------------------------------------

_ : intOf★ Γ★ Θ★ˢ ≡ abst ∷ []        -- Z still abstract (nothing is faked)
_ = refl

bwf★-Θ★ : Γ★ ∣ intOf★ Γ★ Θ★ˢ ⊢ᵇ★ Θ★ˢ
bwf★-Θ★ = bwf★↑ (wf-var here-abst)
                (bwf★↓ (skip-abst here) ≈-refl wf-ℕ bwf★[])

⊢T3★ : [] ∣ [] ⊢★ T3★ ⦂ `∀ `ℕ
⊢T3★ = env★ (bwf★↑ wf-ℕ bwf★[]) (sc-∀ sc-ℕ)
            (⊢★Λ (⊢★· (env★ bwf★-Θ★ (sc-⇒ sc-ℕ sc-ℕ)
                             (⊢★ƛ wf-ℕ (⊢★` here))) ⊢★$))

-- THE DUAL IS WELL FORMED: its conceal of Z is the rep-less one, licensed by
-- the mere existence of the slot (bwf★⋆↓ here-abst).
bwf★-dual : (abst ∷ []) ∣ intOf★ (abst ∷ []) dual⋆ ⊢ᵇ★ dual⋆
bwf★-dual = bwf★⋆ (bwf★↑ wf-ℕ (bwf★⋆↓ here-abst bwf★[]))

-- THE REBUILD IS EXACT: the dual's interior is Γ★ on the nose, so cmax is
-- still what the rebuild needs (dropping cnc⋆ from isConc did NOT drop the
-- slot from the frame).
rebuild-E★ : intOf★ (abst ∷ []) dual⋆ ≡ Γ★
rebuild-E★ = refl

DualInt★-E★ : Γ★ ≼≈ intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆
DualInt★-E★ = ≼≈-refl Γ★

⊢T4★ : [] ∣ [] ⊢★ T4full★ ⦂ `∀ `ℕ
⊢T4★ = env★ (bwf★↑ wf-ℕ bwf★[]) (sc-∀ sc-ℕ)
            (⊢★Λ (env★ bwf★-Θ★ sc-ℕ (env★ bwf★-dual sc-ℕ ⊢★$)))

-- … and the contractum is a VALUE of the program's type: E★ terminates.
val-T4★ : Value★ T4full★
val-T4★ = V★-⟪⟫ (V★-G (G★-Λ (V★-⟪⟫ (V★-⟪⟫ V★-$))))

-- the argument's own retype, isolated: 5 : ℕ inside the dual
⊢arg★ : intOf★ (abst ∷ []) dual⋆ ∣ [] ⊢★ $★ 5 ⦂ substᵗ (γᵇ★ dual⋆) `ℕ
⊢arg★ = ⊢★$

------------------------------------------------------------------------
-- §3.2  DUAL OF DUAL.  dual⋆ CONTAINS a cnc⋆; can it be dualised?  Yes: the
-- reveal for a cnc⋆-dropped slot has no rep, so it comes out rvl⋆★, and the
-- round trip is EXACT (intOf★ Γ★ dd = the original interior).  This is also
-- where today's design breaks independently of E★ (§4.3): the live
-- cncOfRevs mints `cnc j `ℕ` for a rvl⋆, which nothing licenses.
------------------------------------------------------------------------

dd : BCtx★
dd = rvl⋆★ ∷ cnc⋆ 0 ∷ cnc★ 1 `ℕ ∷ []

_ : dualᴳ★ (intOf★ Γ★ Θ★ˢ) dual⋆ ≡ dd
_ = refl

_ : intOf★ Γ★ dd ≡ intOf★ Γ★ Θ★ˢ           -- the round trip
_ = refl

⊢dd : Γ★ ∣ intOf★ Γ★ dd ⊢ᵇ★ dd
⊢dd = bwf★⋆ (bwf★⋆↓ here-abst
              (bwf★↓ (skip-abst here) ≈-refl wf-ℕ bwf★[]))

-- the OTHER cnc⋆ case for a dual: when the exterior DOES know the
-- ⋆-dropped slot, the dual re-reveals the exterior's own knowledge (the
-- ordinary blocked-slot copy) and the rebuild is again exact — a cnc⋆
-- hides nothing, so nothing is leaked by re-revealing it.
_ : dualᴳ★ (rvld `ℕ ∷ []) (cnc⋆ 0 ∷ []) ≡ rvl★ `ℕ ∷ []
_ = refl

_ : intOf★ (intOf★ (rvld `ℕ ∷ []) (cnc⋆ 0 ∷ [])) (rvl★ `ℕ ∷ [])
    ≡ rvld `ℕ ∷ []
_ = refl

------------------------------------------------------------------------
-- §4.  SOUNDNESS HUNT.  cnc⋆ is a conceal with NO premise, so it is the
-- obvious place to try to smuggle a lie back in.  The single barrier is
-- that its slot is `blk`: no boundary type may name it.  §4.2 proves that
-- barrier in GENERAL, and §4.0/§4.1 show what it is holding back.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §4.0  WHY `blk` AND NOT A DUMMY γ-IMAGE.  Had cnc⋆'s slot stayed `ok`
-- (the rvl⋆ treatment: a dummy image nobody consults), a boundary type
-- naming it would get γcnc★'s FALLTHROUGH image — an index shifted for a
-- slot that is not there.  On ↓X:⋆ over X:=∀Z.Z→Z the internal face of
-- B₀ = X comes out ` 0 in the EMPTY interior: a dangling index, i.e. the
-- (env) rule would type a term at a type that does not exist.
------------------------------------------------------------------------

Ξ⋆bad : BCtx★
Ξ⋆bad = cnc⋆ 0 ∷ []

γ-alias-⋆ : substᵗ (γᵇ★ Ξ⋆bad) (` 0) ≡ ` 0
γ-alias-⋆ = refl

_ : intOf★ (rvld ∀ZZ ∷ []) Ξ⋆bad ≡ []
_ = refl

dangling-⋆ : ¬ (intOf★ (rvld ∀ZZ ∷ []) Ξ⋆bad ∋tv 0)
dangling-⋆ ()

------------------------------------------------------------------------
-- §4.1  bad VIA ⋆.  bad = (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫ is refuted
-- today by the reversal premise; cnc⋆ HAS no reversal premise, so the ⋆
-- variant must be refuted by the scope premise instead — and it is.
------------------------------------------------------------------------

bad⋆ : Term★
bad⋆ = (($★ 7) ⟪ Ξ⋆bad , ` 0 ⟫★) ⟪ rvl★ ∀ZZ ∷ [] , ` 0 ⟫★

_ : baseS★ Ξ⋆bad (rvld ∀ZZ ∷ []) ≡ blk ∷ []
_ = refl

¬Scoped-⋆bad : ¬ Scoped (baseS★ Ξ⋆bad (rvld ∀ZZ ∷ [])) (` 0)
¬Scoped-⋆bad (sc-var ())

¬⊢bad⋆ : ¬ ([] ∣ [] ⊢★ bad⋆ ⦂ ∀ZZ)
¬⊢bad⋆ (env★ _ _ (env★ _ sc _)) = ¬Scoped-⋆bad sc

-- and B₀ = X is the ONLY candidate: Ξ⋆bad has no reveal, so its external
-- face is the identity substitution — whatever B₀ is, it IS the outer
-- boundary's demand, so the refutation above covers every B₀.
face-forces-B₀ : ∀ B₁ → substᵗ (ρᵇ★ Ξ⋆bad) B₁ ≡ B₁
face-forces-B₀ B₁ = subst-id B₁

-- the same for bad₂'s shape (Γb = X:=X′ , X′:=∀Z.Z→Z): the ⋆ variant is
-- refused before any knowledge comparison happens
_ : baseS★ (cnc⋆ 0 ∷ rvl★ `ℕ ∷ []) Γb ≡ ok ∷ blk ∷ ok ∷ []
_ = refl

¬Scoped-⋆bad₂ : ¬ Scoped (baseS★ (cnc⋆ 0 ∷ rvl★ `ℕ ∷ []) Γb) (` 1)
¬Scoped-⋆bad₂ (sc-var (thereᵒ ()))

------------------------------------------------------------------------
-- §4.2  THE BARRIER, IN GENERAL.  A ⋆-concealed slot is `blk`, and a
-- `blk` Γ-slot cannot be named by a Scoped boundary type.  (Ported from
-- BReduction's revS-drop / slotsᴳ-ok, which are the same statements for
-- the live boundary.)
------------------------------------------------------------------------

revS-drop★ : ∀ Ξ₁ {Ψ₁ : SCtx} {i} → (revSlots★ Ξ₁ ++ Ψ₁) ∋ok (revs★ Ξ₁ + i)
           → Ψ₁ ∋ok i
revS-drop★ []               p = p
revS-drop★ (rvl★ A ∷ Ξ₁)    p = revS-drop★ Ξ₁ (∋ok-tail p)
revS-drop★ (rvl⋆★ ∷ Ξ₁)     p = revS-drop★ Ξ₁ (∋ok-tail p)
revS-drop★ (cnc★ X A ∷ Ξ₁)  p = revS-drop★ Ξ₁ p
revS-drop★ (cnc⋆ X ∷ Ξ₁)    p = revS-drop★ Ξ₁ p

slotsᴳ★-ok : ∀ Ξ₁ (Γ₁ : TCtx) k j → slotsᴳ★ Ξ₁ k Γ₁ ∋ok j
           → slotAt★ Ξ₁ (k + j) ≡ ok
slotsᴳ★-ok Ξ₁ []       k j       ()
slotsᴳ★-ok Ξ₁ (E ∷ Γ₁) k zero    p rewrite +-identityʳ k = ∋ok-head p
slotsᴳ★-ok Ξ₁ (E ∷ Γ₁) k (suc j) p rewrite +-suc k j =
  slotsᴳ★-ok Ξ₁ Γ₁ (suc k) j (∋ok-tail p)

slotAt★-blk : ∀ Ξ₁ X₁ → isConc★ X₁ Ξ₁ ≡ false → X₁ < cmax★ Ξ₁
            → slotAt★ Ξ₁ X₁ ≡ blk
slotAt★-blk Ξ₁ X₁ ec lt with cmax★ Ξ₁ ≤? X₁
slotAt★-blk Ξ₁ X₁ ec lt | yes le = ⊥-elim (≤⇒≯ le lt)
slotAt★-blk Ξ₁ X₁ ec lt | no ¬le =
  cong (λ b → if b then ok else blk) ec

-- THEOREM (the barrier).  No Scoped boundary type names a dropped slot the
-- boundary does not conceal — the ⋆-concealed slots included.
⋆-unnameable : ∀ Ξ₁ (Γ₁ : TCtx) i → isConc★ i Ξ₁ ≡ false → i < cmax★ Ξ₁
             → ¬ Scoped (baseS★ Ξ₁ Γ₁) (` (revs★ Ξ₁ + i))
⋆-unnameable Ξ₁ Γ₁ i ec lt (sc-var p) =
  ok≢blk (trans (sym (slotsᴳ★-ok Ξ₁ Γ₁ 0 i (revS-drop★ Ξ₁ p)))
                (slotAt★-blk Ξ₁ i ec lt))

-- COROLLARY for (ii) — "does cnc⋆ let a value of VARIABLE type exist at an
-- abstract variable?"  A wrapper's type is substᵗ (ρᵇ★ Ξ) B₀ with B₀ Scoped,
-- so a variable-typed wrapper names either a REVEAL slot of Ξ or an `ok`
-- Γ-slot — and a ⋆-slot is neither.  cnc⋆ therefore adds NO route to a
-- variable-typed value; the two routes that exist are exactly today's
-- (a reveal's rep, or a genuine conceal, which cnc-needs-knowledge kills at
-- an abstract variable).
var-route★ : ∀ Ξ₁ (Γ₁ : TCtx) X₁ → Scoped (baseS★ Ξ₁ Γ₁) (` X₁)
  → (X₁ < revs★ Ξ₁)
  ⊎ (Σ ℕ λ i → (X₁ ≡ revs★ Ξ₁ + i) × (slotAt★ Ξ₁ i ≡ ok))
var-route★ Ξ₁ Γ₁ X₁ (sc-var p) with split (revs★ Ξ₁) X₁
var-route★ Ξ₁ Γ₁ X₁ (sc-var p) | inj₁ lt = inj₁ lt
var-route★ Ξ₁ Γ₁ X₁ (sc-var p) | inj₂ (i , e) =
  inj₂ (i , e , slotsᴳ★-ok Ξ₁ Γ₁ 0 i (revS-drop★ Ξ₁ (∋ok-≡ e p)))

------------------------------------------------------------------------
-- §4.3  A BONUS FINDING, INDEPENDENT OF E★: today's dual of a boundary
-- containing rvl⋆ is ALREADY unlicensable.  cncOfRevs invents the rep `ℕ
-- for a rep-less reveal, and the interior entry for that reveal is `abst`,
-- so bwf↓'s lookup fails exactly as at E★.  cnc⋆ repairs this case too, and
-- it is REACHABLE: E★'s own dual contains a rvl⋆ (§3.2's dual of dual).
------------------------------------------------------------------------

Θr : BCtx
Θr = rvl⋆ ∷ []

_ : intOf [] Θr ≡ abst ∷ []
_ = refl

_ : dualᴳ [] Θr ≡ cnc 0 `ℕ ∷ []          -- an INVENTED rep …
_ = refl

¬DualCnc-rvl⋆ :
  ¬ (Σ Ty λ A₀ → (intOf [] Θr ∋ 0 := A₀)
               × Reversal (dualᴳ [] Θr) 0 `ℕ A₀)
¬DualCnc-rvl⋆ (A₀ , () , _)

_ : dualᴳ★ [] (emb Θr) ≡ cnc⋆ 0 ∷ []     -- … becomes the rep-less conceal
_ = refl

⊢dual-rvl⋆ : (abst ∷ []) ∣ intOf★ (abst ∷ []) (cnc⋆ 0 ∷ [])
             ⊢ᵇ★ (cnc⋆ 0 ∷ [])
⊢dual-rvl⋆ = bwf★⋆↓ here-abst bwf★[]

------------------------------------------------------------------------
-- §4.4  FACES AND cmax.  Adding a cnc⋆ entry changes NEITHER face except
-- through cmax: ρᵇ★ ignores it outright, and γcnc★ ignores it too — cmax is
-- a PARAMETER of γcnc★, so it is the only channel.
------------------------------------------------------------------------

ρᵇ-⋆ : ∀ X₁ Ξ₁ Y → ρᵇ★ (cnc⋆ X₁ ∷ Ξ₁) Y ≡ ρᵇ★ Ξ₁ Y
ρᵇ-⋆ X₁ Ξ₁ Y = refl

γcnc-⋆ : ∀ r m X₁ Ξ₁ Y → γcnc★ r m (cnc⋆ X₁ ∷ Ξ₁) Y ≡ γcnc★ r m Ξ₁ Y
γcnc-⋆ r m X₁ Ξ₁ Y = refl

cmax-⋆-vs-cnc : ∀ X₁ A₁ Ξ₁
              → cmax★ (cnc⋆ X₁ ∷ Ξ₁) ≡ cmax★ (cnc★ X₁ A₁ ∷ Ξ₁)
cmax-⋆-vs-cnc X₁ A₁ Ξ₁ = refl

-- A HAND-WRITTEN cnc⋆ at a high index DOES block more: cnc⋆ 2 over a
-- three-slot Γ drops all three and blocks 0 and 1, which nothing concealed.
Γ3 : TCtx
Γ3 = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

Ξhi : BCtx★
Ξhi = cnc⋆ 2 ∷ []

_ : cmax★ Ξhi ≡ 3
_ = refl

_ : baseS★ Ξhi Γ3 ≡ blk ∷ blk ∷ blk ∷ []
_ = refl

_ : intOf★ Γ3 Ξhi ≡ []
_ = refl

-- … but the DUAL never mints one.  It emits one conceal per reveal, at the
-- contiguous interior indices 0 … revs−1, and its cnc⋆ carries THE SAME
-- INDEX as the cnc it replaces — so cmax of the dual is what the rebuild
-- needs, whichever branch each reveal takes.  (cncOfRevsᵖ is the live,
-- always-conceal block.)
cncOfRevsᵖ : ℕ → BCtx★ → BCtx★
cncOfRevsᵖ j []              = []
cncOfRevsᵖ j (rvl★ A ∷ Ζ)    = cnc★ j A ∷ cncOfRevsᵖ (suc j) Ζ
cncOfRevsᵖ j (rvl⋆★ ∷ Ζ)     = cnc★ j `ℕ ∷ cncOfRevsᵖ (suc j) Ζ
cncOfRevsᵖ j (cnc★ X A ∷ Ζ)  = cncOfRevsᵖ j Ζ
cncOfRevsᵖ j (cnc⋆ X ∷ Ζ)    = cncOfRevsᵖ j Ζ

_ : cncOfRevsᵖ 0 Θ★ˢ ≡ emb (cncOfRevs 0 Θ★)
_ = refl

cmax-cncOfRevs★ : ∀ (Γ₁ : TCtx) Ξ₁ j Ζ
                → cmax★ (cncOfRevs★ Γ₁ Ξ₁ j Ζ) ≡ cmax★ (cncOfRevsᵖ j Ζ)
cmax-cncOfRevs★ Γ₁ Ξ₁ j []              = refl
cmax-cncOfRevs★ Γ₁ Ξ₁ j (rvl⋆★ ∷ Ζ)     =
  cong (suc j ⊔_) (cmax-cncOfRevs★ Γ₁ Ξ₁ (suc j) Ζ)
cmax-cncOfRevs★ Γ₁ Ξ₁ j (cnc★ X A ∷ Ζ)  = cmax-cncOfRevs★ Γ₁ Ξ₁ j Ζ
cmax-cncOfRevs★ Γ₁ Ξ₁ j (cnc⋆ X ∷ Ζ)    = cmax-cncOfRevs★ Γ₁ Ξ₁ j Ζ
cmax-cncOfRevs★ Γ₁ Ξ₁ j (rvl★ A ∷ Ζ) with ⟦ Γ₁ ∣ Ξ₁ ⟧ᴴ★ j A
cmax-cncOfRevs★ Γ₁ Ξ₁ j (rvl★ A ∷ Ζ) | rvld B =
  cong (suc j ⊔_) (cmax-cncOfRevs★ Γ₁ Ξ₁ (suc j) Ζ)
cmax-cncOfRevs★ Γ₁ Ξ₁ j (rvl★ A ∷ Ζ) | abst   =
  cong (suc j ⊔_) (cmax-cncOfRevs★ Γ₁ Ξ₁ (suc j) Ζ)

-- on E★: the ⋆-dual and the (unlicensable) cnc-dual have the same cmax, the
-- same revs, and the same interior
_ : cmax★ dual⋆ ≡ cmax★ (emb dualᵛ)
_ = refl

_ : cmax★ dual⋆ ≡ revs★ Θ★ˢ
_ = refl

_ : intOf★ (abst ∷ []) dual⋆ ≡ intOf★ (abst ∷ []) (emb dualᵛ)
_ = refl

------------------------------------------------------------------------
-- §4.5  WHAT THE FIX BREAKS (the one real cost).  Wrap transports its
-- boundary type through the frame permutation swapᵇ, so its preservation
-- needs the SCOPE TRANSPORT
--
--   Scoped (baseS Θ Δ) B₁  →  Scoped (baseS (dualᴳ Δ Θ) (intOf Δ Θ))
--                                    (renameᵗ (swapᵇ Θ) B₁)
--
-- A reveal slot of Θ is `ok` on the left and becomes the dual's CONCEAL
-- slot, `ok` on the right — today.  With cnc⋆ that slot is `blk`, so the
-- transport FAILS exactly at a reveal the dual re-hides.  Measured on E★
-- (Θ★'s reveal Z is B₁ when f : ∀Z. Z→ℕ):
------------------------------------------------------------------------

sc-transport-live : Scoped (baseS Θ★ Γ★) (` 0)
                  × Scoped (baseS dualᵛ (intOf Γ★ Θ★)) (` 2)
sc-transport-live = sc-var hereᵒ , sc-var (thereᵒ (thereᵒ hereᵒ))

sc-transport-⋆ : Scoped (baseS★ Θ★ˢ Γ★) (` 0)
               × ¬ Scoped (baseS★ dual⋆ (intOf★ Γ★ Θ★ˢ)) (` 2)
sc-transport-⋆ =
  sc-var hereᵒ , λ { (sc-var (thereᵒ (thereᵒ ()))) }

-- So neither regime types that Wrap: the live one fails at the boundary
-- (¬DualCnc-E★), the ⋆ one fails at the scope premise.  Both are saved only
-- by no-abstract-value (§5.2), which is why it stays on the install list.

------------------------------------------------------------------------
-- §4.6  A REVEAL WHOSE REP NAMES A ⋆-CONCEALED SLOT.  Legal (the rep is a
-- plain-exterior type), and it loses its RAW reading — which the hybrid
-- then recovers ambiently.  No cascade, no leak: the exported type X and
-- the interior knowledge ℕ agree because X really is ℕ.
------------------------------------------------------------------------

Γrs : TCtx
Γrs = rvld `ℕ ∷ []

Ξrs : BCtx★
Ξrs = rvl★ (` 0) ∷ cnc⋆ 0 ∷ []          -- ↑W:=X , ↓X:⋆

_ : slotAt★ Ξrs 0 ≡ blk
_ = refl

_ : ⟦ Ξrs ⟧ᵉ★ 0 (` 0) ≡ abst            -- raw: nothing reads through a ⋆-slot
_ = refl

_ : ⟦ Γrs ∣ Ξrs ⟧ᴴ★ 0 (` 0) ≡ rvld `ℕ   -- the hybrid recovers it
_ = refl

⊢Ξrs : Γrs ∣ intOf★ Γrs Ξrs ⊢ᵇ★ Ξrs
⊢Ξrs = bwf★↑ (wf-var here-rvld) (bwf★⋆↓ here-rvld bwf★[])

-- the dual's own copied reveal reps can never name one of ITS ⋆-slots:
-- copyRep shifts every copy up by revs★ Ξ, and the ⋆-conceals sit BELOW
-- that (indices 0 … revs★ Ξ − 1).  Checked on E★'s dual and its dual:
_ : ⟦ intOf★ Γ★ Θ★ˢ ∣ dual⋆ ⟧ᴴ★ 1 `ℕ ≡ rvld `ℕ
_ = refl

------------------------------------------------------------------------
-- §5.  THE COMPLETED DualCnc CASE SPLIT.
--
-- The dual conceals every reveal of Θ at its interior slot j.  Three cases,
-- by the interior entry ⟦ Δ ∣ Θ ⟧ᴴ j A the (a″) design assigns that slot:
--
--   (1) RAW EXPRESSIBLE   entry = rvld B with B the raw reading of the rep
--                         → the dual emits cnc★ j A, licensed against B
--                         (today's case; UpToProbe's DualCnc≈-Pc, and E★'s
--                         own T2 dual below);
--   (2) UNFOLDABLE        the raw reading is blocked but the AMBIENT
--                         unfolding is expressible → same emission, licensed
--                         against the unfolded knowledge, and (Pn's bonus)
--                         the read-back resolves through the dual's own
--                         copied reveal so the premise holds SYNTACTICALLY;
--   (3) NEITHER           entry = abst (Λ-bound blocked rep, or a rvl⋆ that
--                         never had a rep) → the dual emits cnc⋆ j, whose
--                         ONLY premise is that the slot exists.
--
-- Case (3) is DISCHARGED IN GENERAL below (cnc⋆-licensed / bwf-cncOfRevs★):
-- the dual's exterior intOf★ Δ Θ begins with one entry per reveal of Θ, so
-- the slot always exists.  Cases (1) and (2) are the standing (a″)
-- obligation, unchanged by this probe.
------------------------------------------------------------------------

-- every reveal slot of Ξ exists in Ξ's interior, whatever its entry is
revE-lo★ : ∀ (Γ₁ : TCtx) Ξ₁ j Ζ {Ψ₁ : TCtx} {Y}
         → Y < revs★ Ζ → (revEnts★ Γ₁ Ξ₁ j Ζ ++ Ψ₁) ∋tv Y
revE-lo★ Γ₁ Ξ₁ j []              ()
revE-lo★ Γ₁ Ξ₁ j (rvl★ A ∷ Ζ) {Y = zero}  lt       =
  ent-here (⟦ Γ₁ ∣ Ξ₁ ⟧ᴴ★ j A) _
revE-lo★ Γ₁ Ξ₁ j (rvl★ A ∷ Ζ) {Y = suc Y} (s≤s lt) =
  ent-skip _ (revE-lo★ Γ₁ Ξ₁ (suc j) Ζ lt)
revE-lo★ Γ₁ Ξ₁ j (rvl⋆★ ∷ Ζ)  {Y = zero}  lt       = ent-here abst _
revE-lo★ Γ₁ Ξ₁ j (rvl⋆★ ∷ Ζ)  {Y = suc Y} (s≤s lt) =
  ent-skip _ (revE-lo★ Γ₁ Ξ₁ (suc j) Ζ lt)
revE-lo★ Γ₁ Ξ₁ j (cnc★ X A ∷ Ζ) lt = revE-lo★ Γ₁ Ξ₁ j Ζ lt
revE-lo★ Γ₁ Ξ₁ j (cnc⋆ X ∷ Ζ)   lt = revE-lo★ Γ₁ Ξ₁ j Ζ lt

-- THEOREM (case 3, in general).  Every cnc⋆ the dual mints is licensed.
cnc⋆-licensed : ∀ (Γ₁ : TCtx) Ξ₁ j → j < revs★ Ξ₁ → intOf★ Γ₁ Ξ₁ ∋tv j
cnc⋆-licensed Γ₁ Ξ₁ j lt = revE-lo★ Γ₁ Ξ₁ 0 Ξ₁ lt

lt-offset : ∀ j n → j < j + suc n
lt-offset j n =
  subst (λ m → suc j ≤ m) (sym (+-suc j n)) (s≤s (m≤m+n j n))

-- The cnc★ obligation, isolated, entry by entry: what cases (1) and (2)
-- must supply, at exactly the (slot, rep) pairs the dual consults.  Note
-- the shape of the rvl★ premise: it is CONDITIONAL on the interior entry
-- being knowledge, so a reveal in case (3) discharges it VACUOUSLY.
CncKnowledge : TCtx → BCtx★ → TCtx → ℕ → Ty → Set
CncKnowledge Δ₁ Ξ₁ Ψ₁ j A = ∀ B → ⟦ Δ₁ ∣ Ξ₁ ⟧ᴴ★ j A ≡ rvld B
  → (intOf★ Δ₁ Ξ₁ ∋ j := B)
  × Reversal★ (intOf★ Δ₁ Ξ₁) (dualᴳ★ Δ₁ Ξ₁) j A B
  × (Ψ₁ ⊢ A)

data CncOk (Δ₁ : TCtx) (Ξ₁ : BCtx★) (Ψ₁ : TCtx) : ℕ → BCtx★ → Set where
  co[]    : ∀ {j} → CncOk Δ₁ Ξ₁ Ψ₁ j []
  co-rvl  : ∀ {j A Ζ} → CncKnowledge Δ₁ Ξ₁ Ψ₁ j A
          → CncOk Δ₁ Ξ₁ Ψ₁ (suc j) Ζ → CncOk Δ₁ Ξ₁ Ψ₁ j (rvl★ A ∷ Ζ)
  co-rvl⋆ : ∀ {j Ζ} → CncOk Δ₁ Ξ₁ Ψ₁ (suc j) Ζ
          → CncOk Δ₁ Ξ₁ Ψ₁ j (rvl⋆★ ∷ Ζ)
  co-cnc  : ∀ {j X A Ζ} → CncOk Δ₁ Ξ₁ Ψ₁ j Ζ
          → CncOk Δ₁ Ξ₁ Ψ₁ j (cnc★ X A ∷ Ζ)
  co-cnc⋆ : ∀ {j X Ζ} → CncOk Δ₁ Ξ₁ Ψ₁ j Ζ
          → CncOk Δ₁ Ξ₁ Ψ₁ j (cnc⋆ X ∷ Ζ)

-- THEOREM.  The dual's whole conceal block is well formed as soon as the
-- cnc★ cases are — the cnc⋆ cases need nothing beyond cnc⋆-licensed.
bwf-cncOfRevs★ : ∀ (Δ₁ : TCtx) Ξ₁ {Ψ₁ : TCtx} j Ζ → CncOk Δ₁ Ξ₁ Ψ₁ j Ζ
  → j + revs★ Ζ ≡ revs★ Ξ₁
  → Bwf★ (intOf★ Δ₁ Ξ₁) Ψ₁ (dualᴳ★ Δ₁ Ξ₁) (cncOfRevs★ Δ₁ Ξ₁ j Ζ)
bwf-cncOfRevs★ Δ₁ Ξ₁ j []             co[]         e = bwf★[]
bwf-cncOfRevs★ Δ₁ Ξ₁ j (cnc★ X A ∷ Ζ) (co-cnc c)   e =
  bwf-cncOfRevs★ Δ₁ Ξ₁ j Ζ c e
bwf-cncOfRevs★ Δ₁ Ξ₁ j (cnc⋆ X ∷ Ζ)   (co-cnc⋆ c)  e =
  bwf-cncOfRevs★ Δ₁ Ξ₁ j Ζ c e
bwf-cncOfRevs★ Δ₁ Ξ₁ j (rvl⋆★ ∷ Ζ)    (co-rvl⋆ c)  e =
  bwf★⋆↓ (cnc⋆-licensed Δ₁ Ξ₁ j
           (subst (λ m → j < m) e (lt-offset j (revs★ Ζ))))
         (bwf-cncOfRevs★ Δ₁ Ξ₁ (suc j) Ζ c
           (trans (sym (+-suc j (revs★ Ζ))) e))
bwf-cncOfRevs★ Δ₁ Ξ₁ j (rvl★ A ∷ Ζ) (co-rvl h c) e
  with ⟦ Δ₁ ∣ Ξ₁ ⟧ᴴ★ j A | h
bwf-cncOfRevs★ Δ₁ Ξ₁ j (rvl★ A ∷ Ζ) (co-rvl h c) e | rvld B | hB =
  bwf★↓ (proj₁ (hB B refl))
        (proj₁ (proj₂ (hB B refl)))
        (proj₂ (proj₂ (hB B refl)))
        (bwf-cncOfRevs★ Δ₁ Ξ₁ (suc j) Ζ c
          (trans (sym (+-suc j (revs★ Ζ))) e))
bwf-cncOfRevs★ Δ₁ Ξ₁ j (rvl★ A ∷ Ζ) (co-rvl h c) e | abst   | hB =
  bwf★⋆↓ (cnc⋆-licensed Δ₁ Ξ₁ j
           (subst (λ m → j < m) e (lt-offset j (revs★ Ζ))))
         (bwf-cncOfRevs★ Δ₁ Ξ₁ (suc j) Ζ c
           (trans (sym (+-suc j (revs★ Ζ))) e))

DualCnc★ : Set
DualCnc★ = ∀ {Δ₁ : TCtx} {Ξ₁ : BCtx★}
  → CncOk Δ₁ Ξ₁ (intOf★ (intOf★ Δ₁ Ξ₁) (dualᴳ★ Δ₁ Ξ₁)) 0 Ξ₁
  → Bwf★ (intOf★ Δ₁ Ξ₁) (intOf★ (intOf★ Δ₁ Ξ₁) (dualᴳ★ Δ₁ Ξ₁))
         (dualᴳ★ Δ₁ Ξ₁) (cncOfRevs★ Δ₁ Ξ₁ 0 Ξ₁)

dualCnc★ : DualCnc★
dualCnc★ {Δ₁} {Ξ₁} c = bwf-cncOfRevs★ Δ₁ Ξ₁ 0 Ξ₁ c refl

------------------------------------------------------------------------
-- §5.1  The three cases, on witnesses.
------------------------------------------------------------------------

-- CASE 1 (raw expressible): E★'s own T2 dual, ↑X:=ℕ ↦ ↓X:=ℕ.
_ : dualᴳ★ [] Θ1★ ≡ cnc★ 0 `ℕ ∷ []
_ = refl

⊢dual-case1 : (rvld `ℕ ∷ []) ∣ intOf★ (rvld `ℕ ∷ []) (cnc★ 0 `ℕ ∷ [])
              ⊢ᵇ★ (cnc★ 0 `ℕ ∷ [])
⊢dual-case1 = bwf★↓ here ≈-refl wf-ℕ bwf★[]

-- CASE 2 (unfoldable): Pn (UpToProbe §5) — Y:=ℕ , X:=ℕ with ↑Z:=Y , ↓X:=ℕ.
-- The raw reading of Z's rep is blocked; the hybrid retries at unfoldᵉ and
-- gets Z:=ℕ, and the dual's read-back resolves through its own copied ↑Y:=ℕ.
ΓPn : TCtx
ΓPn = rvld `ℕ ∷ rvld `ℕ ∷ []

ΘPn : BCtx★
ΘPn = cnc★ 1 `ℕ ∷ rvl★ (` 0) ∷ []

_ : ⟦ ΓPn ∣ ΘPn ⟧ᴴ★ 0 (` 0) ≡ rvld `ℕ      -- the hybrid fires
_ = refl

_ : intOf★ ΓPn ΘPn ≡ rvld `ℕ ∷ []
_ = refl

_ : dualᴳ★ ΓPn ΘPn ≡ rvl★ `ℕ ∷ rvl★ `ℕ ∷ cnc★ 0 (` 0) ∷ []
_ = refl

⊢dual-case2 : intOf★ ΓPn ΘPn
            ∣ intOf★ (intOf★ ΓPn ΘPn) (dualᴳ★ ΓPn ΘPn) ⊢ᵇ★ dualᴳ★ ΓPn ΘPn
⊢dual-case2 =
  bwf★↑ wf-ℕ (bwf★↑ wf-ℕ (bwf★↓ here ≈-refl (wf-var here-rvld) bwf★[]))

_ : intOf★ (intOf★ ΓPn ΘPn) (dualᴳ★ ΓPn ΘPn) ≡ ΓPn    -- exact rebuild
_ = refl

-- and case 2 INSTANTIATES the general theorem: its one knowledge premise is
-- real, and the conceal block follows
knowPn : CncKnowledge ΓPn ΘPn ΓPn 0 (` 0)
knowPn B refl = here , ≈-refl , wf-var here-rvld

cncOk-Pn : CncOk ΓPn ΘPn ΓPn 0 ΘPn
cncOk-Pn = co-cnc (co-rvl knowPn co[])

bwf-cnc-Pn : Bwf★ (intOf★ ΓPn ΘPn) ΓPn (dualᴳ★ ΓPn ΘPn)
                  (cncOfRevs★ ΓPn ΘPn 0 ΘPn)
bwf-cnc-Pn = dualCnc★ cncOk-Pn

-- CASE 3 (neither): E★ itself — and here the general theorem discharges the
-- obligation with NO knowledge hypothesis at all: the rvl★ premise is
-- VACUOUS, because Z's interior entry is abstract.
cncOk-E★ : CncOk Γ★ Θ★ˢ (intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆) 0 Θ★ˢ
cncOk-E★ = co-rvl (λ B ()) (co-cnc co[])

bwf-cnc-E★ : Bwf★ (intOf★ Γ★ Θ★ˢ) (intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆)
                  (dualᴳ★ Γ★ Θ★ˢ) (cncOfRevs★ Γ★ Θ★ˢ 0 Θ★ˢ)
bwf-cnc-E★ = dualCnc★ cncOk-E★

-- (the same block, spelled out by hand, is bwf★-dual's tail in §3.1, and
-- ⊢dual-rvl⋆ in §4.3 is the rvl⋆ instance)

------------------------------------------------------------------------
-- §5.2  IS no-abstract-value STILL NEEDED?  YES — but its JOB MOVES.
--
-- It is no longer needed for DualCnc (case 3 is now a theorem).  It is
-- needed for the ARGUMENT side of Wrap, in exactly the shape the mandate
-- names: B₁ mentioning a reveal Z whose knowledge is inexpressible.  Take
-- E★ with f : ∀Z. Z→ℕ instead of ∀Z. ℕ→ℕ; then B₁ = Z = ` 0 over Θ★'s
-- frame, and swapᵇ sends it to the dual's slot 2.
------------------------------------------------------------------------

_ : swapᵇ★ Θ★ˢ 0 ≡ 2
_ = refl

_ : baseS★ dual⋆ (intOf★ Γ★ Θ★ˢ) ≡ blk ∷ ok ∷ blk ∷ []
_ = refl

-- with the fix, the dual's boundary type may NOT name Z: unScoped …
⋆-blocks-B₁ : ¬ Scoped (baseS★ dual⋆ (intOf★ Γ★ Θ★ˢ))
                       (` (swapᵇ★ Θ★ˢ 0))
⋆-blocks-B₁ (sc-var (thereᵒ (thereᵒ ())))

-- … and rightly so: its γ face would be a DANGLING index (Γ★ has 2 slots),
-- so the case is not merely unprovable, it is meaningless.
γ-face-⋆-dangling : substᵗ (γᵇ★ dual⋆) (` 2) ≡ ` 2
γ-face-⋆-dangling = refl

¬Γ★∋2 : ¬ (Γ★ ∋tv 2)
¬Γ★∋2 (skip-abst (skip-rvld ()))

-- the LIVE dual's γ face at that slot IS meaningful (it is Y = ` 0) — the
-- live design fails at the boundary instead (¬DualCnc-E★).  So in BOTH
-- regimes the shape is stuck, and what rules the REDEX out is the type of
-- the argument such a B₁ demands: substᵗ (ρᵇ Θ★) (` 0) = ` 0 = Y, with Y
-- ABSTRACT in Γ★.  That is no-abstract-value's hypothesis exactly.
_ : substᵗ (γᵇ dualᵛ) (` 2) ≡ ` 0
_ = refl

_ : substᵗ (ρᵇ Θ★) (` 0) ≡ ` 0
_ = refl

_ : entAt Γ★ 0 ≡ abst
_ = refl

NoAbstractValue★ : Set
NoAbstractValue★ = ∀ {Δ₁ : TCtx} {V₁ : Term★} {X₁}
  → Value★ V₁ → Δ₁ ∣ [] ⊢★ V₁ ⦂ ` X₁ → entAt Δ₁ X₁ ≡ abst → ⊥

-- its first base survives the extension unchanged …
val-var-wrapper★ : ∀ {Δ₁ Γ₁ X₁} → Value★ V★ → Δ₁ ∣ Γ₁ ⊢★ V★ ⦂ ` X₁
  → Σ Term★ λ V' → Σ BCtx★ λ Ξ' → Σ Ty λ B' → V★ ≡ V' ⟪ Ξ' , B' ⟫★
val-var-wrapper★ V★-$           ()
val-var-wrapper★ (V★-G G★-ƛ)    ()
val-var-wrapper★ (V★-G (G★-Λ _)) ()
val-var-wrapper★ (V★-⟪⟫ {V★ = V'} {Ξ⋆ = Ξ'} {B₀ = B'} _) _ =
  V' , Ξ' , B' , refl

-- … and cnc⋆ adds NO CASE to its induction: var-route★ (§4.2) says a
-- variable-typed wrapper names a reveal slot or an `ok` Γ-slot, and a
-- ⋆-slot is neither.  So the lemma's proof obligation is the same as
-- before this probe; only its USE SITE moves (DualCnc ⇒ Wrap's argument).

------------------------------------------------------------------------
-- §6.  RENAMING, RETAG, ∋:=-TRANSPORT.  All trivial for cnc⋆, and
-- strictly cheaper than for cnc: there is no rep, so the interior renaming
-- never touches it, and its premise is ∋tv, not ∋:=.
------------------------------------------------------------------------

ren-⋆-index : ∀ ρ ir X₁ Ξ₁
            → renᴮ★ ρ ir (cnc⋆ X₁ ∷ Ξ₁) ≡ cnc⋆ (ρ X₁) ∷ renᴮ★ ρ ir Ξ₁
ren-⋆-index ρ ir X₁ Ξ₁ = refl

ren-⋆-cmax : ∀ ρ ir X₁ A₁ Ξ₁
           → cmax★ (renᴮ★ ρ ir (cnc⋆ X₁ ∷ Ξ₁))
           ≡ cmax★ (renᴮ★ ρ ir (cnc★ X₁ A₁ ∷ Ξ₁))
ren-⋆-cmax ρ ir X₁ A₁ Ξ₁ = refl

ren-⋆-isConc : ∀ ρ ir i X₁ Ξ₁
             → isConc★ i (renᴮ★ ρ ir (cnc⋆ X₁ ∷ Ξ₁))
             ≡ isConc★ i (renᴮ★ ρ ir Ξ₁)
ren-⋆-isConc ρ ir i X₁ Ξ₁ = refl

ren-⋆-revEnts : ∀ (Γ₁ : TCtx) Ξ₁ j X₁ Ζ
              → revEnts★ Γ₁ Ξ₁ j (cnc⋆ X₁ ∷ Ζ) ≡ revEnts★ Γ₁ Ξ₁ j Ζ
ren-⋆-revEnts Γ₁ Ξ₁ j X₁ Ζ = refl

-- E★'s dual under a renaming: the index moves, nothing else does
_ : renᴮ★ suc (intRen★ suc dual⋆) dual⋆
    ≡ rvl⋆★ ∷ rvl★ `ℕ ∷ cnc⋆ 1 ∷ []
_ = refl

-- the ONE premise to transport, and it rides the ≼≈ LENGTH (where cnc★
-- needs ≼≈-∋:= plus a fresh ≈-comparison of the reps)
≼≈-∋tv : ∀ {Δ₁ Δ₂ : TCtx} {X₁} → Δ₁ ≼≈ Δ₂ → Δ₁ ∋tv X₁ → Δ₂ ∋tv X₁
≼≈-∋tv p = ∋tv-len (≼≈-len p)

-- a NON-TRIVIAL retag instance: UpToProbe's Γq (raw chained knowledge)
-- against its unfolded rebuild.  A cnc⋆ premise crosses it by ≼≈-∋tv …
⋆-retag-Γq : intOfᴴ (intOfᴴ Γq Θq) (dualᴳ≈ Γq Θq) ∋tv 0
⋆-retag-Γq = ≼≈-∋tv DualInt≈-Γq here-rvld

-- … while a cnc★ premise must re-establish its knowledge up to ≈
cnc-retag-Γq : Σ Ty λ A₀' → (Γq′ ∋ 0 := A₀') × ((` 0) ≈Δ̄[ Γq′ ↓ 0 ] A₀')
cnc-retag-Γq = ≼≈-∋:= DualInt≈-Γq here

-- and on E★ the rebuild is EXACT, so both are the identity
⋆-retag-E★ : intOf★ (intOf★ Γ★ Θ★ˢ) dual⋆ ∋tv 0
⋆-retag-E★ = ≼≈-∋tv DualInt★-E★ here-abst

------------------------------------------------------------------------
-- §7.  A NEW COUNTEREXAMPLE: E★′.  cnc⋆ IS NOT SUFFICIENT.
--
--   E★′ = (ΛX. λf:(∀Z. (Z→ℕ)→(Z→ℕ)). ΛY. f [Y] (λy:Y. 5)) [ℕ]
--           · (ΛZ. λg:(Z→ℕ). λz:Z. g z)                     : ∀Y. Y→ℕ
--
-- Same shape as E★, with ONE change: the instantiated ∀-body MENTIONS its
-- own variable, so the failing Wrap's B₁ is Z→ℕ.  Now
--   * the argument is `λy:Y. 5`, a VALUE at an ARROW type — so
--     no-abstract-value is silent here too (its hypothesis is a variable
--     type), and the redex is genuinely REACHABLE;
--   * with cnc⋆ the dual re-hides Z, and a re-hidden slot is `blk`, so the
--     dual CANNOT carry the boundary type ` 2 ⇒ `ℕ that the argument needs:
--     the contractum is untypable for the scope premise instead;
--   * the LIVE (rep-carrying) dual's two faces are EXACTLY right at that
--     boundary type (face-int-E★′ / face-ext-E★′ below) — its sole defect
--     is bwf↓'s knowledge lookup.
-- So the obstruction is not "the dual asserts something it cannot know" but
-- "the dual must TRANSLATE a type that mentions Z", which a rep-less
-- conceal cannot do.  That is DECISIONS.md's candidate (b) (a dual-only
-- conceal licensed by the reveal it cancels), with cnc⋆ still needed for the
-- rvl⋆ case (§4.3), where there is no rep to copy.
------------------------------------------------------------------------

polyg : Ty                     -- ∀Z. (Z→ℕ)→(Z→ℕ)
polyg = `∀ ((` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ))

B₀′ : Ty
B₀′ = (` 0 ⇒ `ℕ) ⇒ (` 0 ⇒ `ℕ)

Bprog′ : Ty
Bprog′ = polyg ⇒ `∀ (` 0 ⇒ `ℕ)

idg : Term                     -- ΛZ. λg:(Z→ℕ). λz:Z. g z
idg = Λ (ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0))))

argY : Term                    -- λy:Y. 5   — a VALUE at type Y→ℕ
argY = ƛ ` 0 ∙ ($ 5)

fn′ : Term
fn′ = ƛ polyg ∙ (Λ (((` 0) ·[ B₀′ , ` 0 ]) · argY))

T0′ T1′ T2′ T3′ W′ T4′ T4full′ : Term
T0′ = ((Λ fn′) ·[ Bprog′ , `ℕ ]) · idg
T1′ = (fn′ ⟪ Θ1 , Bprog′ ⟫) · idg
T2′ = (Λ (((idg ⟪ Θd′ , polyg ⟫) ·[ B₀′ , ` 0 ]) · argY))
      ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T3′ = (Λ ((((ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0)))) ⟪ Θ★ , B₀′ ⟫)
           · argY))) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
W′  = argY ⟪ dualᵛ , (` 2 ⇒ `ℕ) ⟫
T4′ = (ƛ ` 0 ∙ (W′ · (` 0))) ⟪ Θ★ , ` 0 ⇒ `ℕ ⟫
T4full′ = (Λ T4′) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫

step01′ : [] ⊢ T0′ -→ T1′
step01′ = ξ-·-l (TyBeta (V-G G-ƛ))

step12′ : [] ⊢ T1′ -→ T2′
step12′ = Wrap (V-G (G-Λ (V-G G-ƛ)))

step23′ : [] ⊢ T2′ -→ T3′
step23′ = ξ-⟪⟫ (ξ-Λ (ξ-·-l (TyWrap (V-G G-ƛ))))

step34′ : [] ⊢ T3′ -→ T4full′
step34′ = ξ-⟪⟫ (ξ-Λ (Wrap (V-G G-ƛ)))

wf-polyg : ∀ {Δ₁ : TCtx} → Δ₁ ⊢ polyg
wf-polyg = wf-∀ (wf-⇒ (wf-⇒ (wf-var here-abst) wf-ℕ)
                      (wf-⇒ (wf-var here-abst) wf-ℕ))

sc-polyg : ∀ {Ψ₁ : SCtx} → Scoped Ψ₁ polyg
sc-polyg = sc-∀ (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
                      (sc-⇒ (sc-var hereᵒ) sc-ℕ))

⊢idg : ∀ {Δ₁ : TCtx} {Γ₁ : Ctx} → Δ₁ ∣ Γ₁ ⊢ idg ⦂ polyg
⊢idg = ⊢Λ (⊢ƛ (wf-⇒ (wf-var here-abst) wf-ℕ)
              (⊢ƛ (wf-var here-abst) (⊢· (⊢` (there here)) (⊢` here))))

⊢argY : Γ★ ∣ [] ⊢ argY ⦂ (` 0 ⇒ `ℕ)
⊢argY = ⊢ƛ (wf-var here-abst) ⊢$

argY-val : Value argY
argY-val = V-G G-ƛ

⊢fn′ : ∀ {Δ₁ : TCtx} → Δ₁ ∣ [] ⊢ fn′ ⦂ Bprog′
⊢fn′ = ⊢ƛ wf-polyg
          (⊢Λ (⊢· (⊢·[] (⊢` here) (wf-var here-abst))
                  (⊢ƛ (wf-var here-abst) ⊢$)))

⊢T0′ : [] ∣ [] ⊢ T0′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T0′ = ⊢· (⊢·[] (⊢Λ ⊢fn′) wf-ℕ) ⊢idg

⊢T1′ : [] ∣ [] ⊢ T1′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T1′ = ⊢· (env (bwf↑ wf-ℕ bwf[])
               (sc-⇒ sc-polyg (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ)))
               ⊢fn′) ⊢idg

⊢T2′ : [] ∣ [] ⊢ T2′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T2′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
           (⊢Λ (⊢· (⊢·[] (env (bwf↓ (skip-abst here) refl wf-ℕ bwf[])
                              sc-polyg ⊢idg)
                         (wf-var here-abst))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

⊢T3′ : [] ∣ [] ⊢ T3′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T3′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
           (⊢Λ (⊢· (env bwf-Θ★
                        (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
                              (sc-⇒ (sc-var hereᵒ) sc-ℕ))
                        (⊢ƛ (wf-⇒ (wf-var here-abst) wf-ℕ)
                            (⊢ƛ (wf-var here-abst)
                                (⊢· (⊢` (there here)) (⊢` here)))))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

-- the LIVE regime: still stuck at the dual's conceal of Z …
¬⊢T4′ : ¬ (Γ★ ∣ [] ⊢ T4′ ⦂ (` 0 ⇒ `ℕ))
¬⊢T4′ (env _ _ (⊢ƛ _ (⊢· (env (bwf⋆ (bwf↑ _ (bwf↓ () _ _ _))) _ _) _)))

-- … and both of the live dual's FACES are exactly what the step needs, at
-- exactly the boundary type Wrap hands it: the argument's own type Y→ℕ
-- inside, and the interior's demand Z→ℕ outside.
face-int-E★′ : substᵗ (γᵇ dualᵛ) (` 2 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
face-int-E★′ = refl

face-ext-E★′ : substᵗ (ρᵇ dualᵛ) (` 2 ⇒ `ℕ)
             ≡ substᵗ (γᵇ Θ★) (` 0 ⇒ `ℕ)
face-ext-E★′ = refl

sc-live-E★′ : Scoped (baseS dualᵛ (intOf Γ★ Θ★)) (` 2 ⇒ `ℕ)
sc-live-E★′ = sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) sc-ℕ

-- THE ⋆ REGIME: the dual is well formed now, but the boundary type it must
-- carry names the RE-HIDDEN slot, which is blk.  Stuck again — for the
-- scope premise this time.
W′⋆ : Term★
W′⋆ = (embT argY) ⟪ dual⋆ , (` 2 ⇒ `ℕ) ⟫★

T4′⋆ : Term★
T4′⋆ = (ƛ★ (` 0) ∙ (W′⋆ ·★ (`★ 0))) ⟪ Θ★ˢ , ` 0 ⇒ `ℕ ⟫★

step34′⋆ : [] ⊢★ embT T3′
           -→★ (Λ★ T4′⋆) ⟪ Θ1★ , `∀ (` 0 ⇒ `ℕ) ⟫★
step34′⋆ = ξ★-⟪⟫ (ξ★-Λ (Wrap★ (V★-G G★-ƛ)))

¬Scoped-⋆-E★′ : ¬ Scoped (baseS★ dual⋆ (intOf★ Γ★ Θ★ˢ)) (` 2 ⇒ `ℕ)
¬Scoped-⋆-E★′ (sc-⇒ (sc-var (thereᵒ (thereᵒ ()))) _)

¬⊢T4′⋆ : ¬ (Γ★ ∣ [] ⊢★ T4′⋆ ⦂ (` 0 ⇒ `ℕ))
¬⊢T4′⋆ (env★ _ _ (⊢★ƛ _ (⊢★· (env★ _ sc _) _))) = ¬Scoped-⋆-E★′ sc

-- and no-abstract-value cannot help: the argument is a value at an ARROW
-- type, in a context where Y is abstract — a perfectly ordinary λ.
vacuity-silent′ : ¬ ((` 0 ⇒ `ℕ) ≡ ` X)
vacuity-silent′ ()

------------------------------------------------------------------------
-- §8.  VERDICT
--
-- E★ VERIFIED (§1), with two index corrections to the memo's trace: the
-- dual's conceal is ↓X:=ℕ at index 1 under the ΛY (⇑ᵀ renames it), and the
-- dual's entries come out ↑Y:⋆ , ↑X:=ℕ , ↓Z:⋆ in that order.  All four
-- steps are live `_⊢_-→_` inhabitants (step01 … step34), T0 … T3 all type
-- at ∀Y.ℕ, and T4 fails in all three regimes (¬⊢T4, ¬⊢T4≈, ¬DualCnc-E★,
-- ¬DualCnc≈ᴴ-E★).  The supervisor's point stands: the argument is `$ 5` at
-- `ℕ, so no-abstract-value is silent (vacuity-silent) — the Λ-bound residue
-- is NOT vacuous.
--
-- THE FIX WORKS ON E★ (§3): ⊢T3★, step34★, ⊢T4★, val-T4★, rebuild-E★,
-- DualInt★-E★, and the dual of the dual round-trips (§3.2: ⊢dd).
--
-- THE FIX IS NOT SUFFICIENT (§7): E★′ — the same program with the ∀-body
-- mentioning its own variable — is a reachable Wrap redex whose contractum
-- types in NEITHER regime (¬⊢T4′ live, ¬⊢T4′⋆ starred), and vacuity is
-- silent there too (the argument is a λ at Y→ℕ).  The live dual's faces are
-- already exactly right (face-int-E★′, face-ext-E★′, sc-live-E★′): the sole
-- defect is bwf↓'s knowledge lookup.  So the design needs candidate (b) —
-- a dual-minted conceal licensed by the reveal it cancels, KEEPING the rep
-- — with cnc⋆ retained only where there is no rep to keep (§4.3's rvl⋆,
-- which today's cncOfRevs mis-handles by inventing `ℕ).
--
-- SOUNDNESS OF cnc⋆ ITSELF: clean.  bad-via-⋆ is refuted by the scope
-- premise (¬⊢bad⋆, and face-forces-B₀ shows B₀ = X is the only candidate);
-- the ⋆-slot is unnameable in general (⋆-unnameable); cnc⋆ adds no route to
-- a variable-typed value (var-route★), so no-abstract-value gains no case;
-- both faces are unchanged except through cmax (ρᵇ-⋆, γcnc-⋆), and the
-- dual's cnc⋆ carries the same index as the cnc it replaces
-- (cmax-cncOfRevs★), so it never blocks more slots than the rebuild needs
-- (a hand-written cnc⋆ at a high index does: Ξhi).  Renaming and retag are
-- trivial (§6): no rep to rename, and the premise rides ∋tv (≼≈-∋tv) rather
-- than ∋:=.
--
-- DualCnc, COMPLETED (§5): cases (1) raw / (2) unfoldable emit cnc★ and are
-- the standing (a″) obligation (⊢dual-case1, ⊢dual-case2, bwf-cnc-Pn);
-- case (3) emits cnc⋆ and is now a THEOREM (cnc⋆-licensed, bwf-cncOfRevs★,
-- dualCnc★) — E★ discharges it with no knowledge hypothesis at all
-- (cncOk-E★, bwf-cnc-E★).  no-abstract-value is therefore NO LONGER needed
-- for DualCnc; it is still needed — and still insufficient — for Wrap's
-- ARGUMENT, where cnc⋆ costs the swapᵇ scope transport (§4.5:
-- sc-transport-live vs sc-transport-⋆).
--
-- ONE THING ARGUED, NOT PROVED: the dual's copied reveal reps can never
-- name one of its own ⋆-slots, because copyRep shifts every copy up by
-- revs★ Ξ while the ⋆-conceals sit below that.  Checked on E★ and its dual
-- of dual; a general proof needs a free-variable lemma for renameᵗ (n +_).
------------------------------------------------------------------------
