module strong.notes.InstallGauntlet where

-- THE INSTALL GAUNTLET for the dual-conceal licence design
-- (notes/DualLicenseDesign.md; the four probes now under notes/old/).
--
-- Everything here is run against the LIVE definitions — strong.Boundary,
-- strong.BReduction — with no local copies of anything.  It is deliberately
-- NOT in strong/All.agda: it is evidence, not development.
--
-- CONTENTS
--   §1  E★′ END TO END.  The counterexample that motivated the whole
--       design: a reachable Wrap redex whose contractum typed in NEITHER
--       the rep-keeping nor the rep-less regime.  All four steps are live
--       `_⊢_-→_` inhabitants, T0′ … T3′ type, and the CONTRACTUM now types
--       — through (bwf-↓x), with the dual's own ↑Y:⋆ supplying the
--       claims-nothing premise.
--   §2  E★ END TO END, the cnc⋆ path — and the finding that with the
--       x-licence E★ needs NO cnc⋆ at all; cnc⋆ is needed for the dual of a
--       REP-LESS reveal, which is what §4's dual-of-dual mints.
--   §3  Pn — the case the AMBIENT unfold retry used to close, and the
--       machine-checked reason it is now a DualCnc≈ residue.
--   §4  DUAL-OF-DUAL on E★′'s shapes: exact round trip, cnc⋆ retained
--       exactly where a rep-less reveal has to be re-hidden.
--   §5  Pc's CHAINED-COPY site: the dual's SECOND-CHANCE copy recovers the
--       knowledge the raw guard refuses, and the rebuild is one unfolding
--       away — which _≼≈_ absorbs and ⊢retag≈ consumes.
--   §6  SOUNDNESS: bad / bad₂ refuted, near-bad admitted, far-bad refused,
--       the ⊢3n-adv adversary refuted (and refuted UNDER ≈ — the §5(ii)
--       gauntlet item), the conceal of a plain Λ-bound variable refused.
--   §7  RENAMING: a transport instance that touches an xrvld entry, and the
--       counter-instance showing why (bwf-↓x)'s rep comparison can be
--       neither ≡ nor ≈Δ̄.
--   §8  THE SkelEq REPAIR: the premise discharged at the dual's birth by
--       xrep-stored, surviving §7b's weakening, refusing the soundness hole
--       the comparison-free licence had, and leaving ⊢3n-adv to starOnly.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context
open import strong.Unfold
open import strong.Boundary
open import strong.BReduction
open import strong.DualDef using (xrep-stored; dual-cnc-skel)

------------------------------------------------------------------------
-- §1.  E★′, END TO END
--
--   E★′ = (ΛX. λf:(∀Z.(Z→ℕ)→(Z→ℕ)). ΛY. (f [Y]) (λy:Y. 5)) [ℕ]
--           · (ΛZ. λg:(Z→ℕ). λz:Z. g z)      : ∀Y. Y→ℕ
--
-- At the ξ TyWrap(Z) step the boundary  ↑Z:=Y , ↓X:=ℕ  is minted at
-- exterior  Y (Λ-bound) , X:=ℕ .  The knowledge "Z is Y" is inexpressible
-- in the interior (Y is blocked) and un-unfoldable (Y is Λ-bound), so Z's
-- entry is the EXTERIOR-READ one.  The later Wrap's dual conceals Z with
-- that very rep, licensed by (bwf-↓x).
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

Θ1 : BCtx                      -- ↑X:=ℕ, the boundary TyBeta is born with
Θ1 = rvl `ℕ ∷ []

Θd′ : BCtx                     -- ↓X:=ℕ, under the ΛY (index 1)
Θd′ = cnc 1 `ℕ ∷ []

Γ★ : TCtx                      -- Y (Λ-bound, 0) , X:=ℕ (1)  — Boundary's Γ₈
Γ★ = Γ₈

Θ★ : BCtx                      -- ↑Z:=Y , ↓X:=ℕ, minted by TyWrap at Γ★
Θ★ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []

-- the LIVE dual at the failing step: ↑Y:⋆ (Y is Λ-bound, so REP-LESS),
-- ↑X:=ℕ (copied from Θ★'s conceal rep), ↓Z:=Y (the once-unlicensable one)
dualᵛ : BCtx
dualᵛ = rvl⋆ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ Γ★ Θ★ ≡ dualᵛ
_ = refl

W′ : Term
W′ = argY ⟪ dualᵛ , (` 2 ⇒ `ℕ) ⟫

T0′ T1′ T2′ T3′ T4′ T4full′ : Term
T0′ = ((Λ fn′) ·[ Bprog′ , `ℕ ]) · idg
T1′ = (fn′ ⟪ Θ1 , Bprog′ ⟫) · idg
T2′ = (Λ (((idg ⟪ Θd′ , polyg ⟫) ·[ B₀′ , ` 0 ]) · argY))
      ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T3′ = (Λ ((((ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0)))) ⟪ Θ★ , B₀′ ⟫)
           · argY))) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T4′ = (ƛ ` 0 ∙ (W′ · (` 0))) ⟪ Θ★ , ` 0 ⇒ `ℕ ⟫
T4full′ = (Λ T4′) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫

------------------------------------------------------------------------
-- §1.1  the steps, by the LIVE reduction relation.
--
-- UNDER PEEL each of the two old Wrap steps becomes TWO: the peel moves
-- the application inside the boundary and wraps the argument in the dual;
-- the ƛ is untouched, and the ordinary Beta consumes it one step later,
-- INSIDE the boundary (ξ-⟪⟫).  The intermediate terms T1½′ / T3½′ are the
-- only new inhabitants; T2′ and T4full′ are reached UNCHANGED.
------------------------------------------------------------------------

T1½′ T3½′ : Term
T1½′ = (fn′ · (idg ⟪ dualᴳ [] Θ1 , polyg ⟫)) ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫
T3½′ = (Λ (((ƛ (` 0 ⇒ `ℕ) ∙ (ƛ ` 0 ∙ ((` 1) · (` 0)))) · W′)
             ⟪ Θ★ , ` 0 ⇒ `ℕ ⟫))
       ⟪ Θ1 , `∀ (` 0 ⇒ `ℕ) ⟫

step01′ : [] ⊢ T0′ -→ T1′
step01′ = ξ-·-l (TyBeta (V-G G-ƛ))

step12a′ : [] ⊢ T1′ -→ T1½′
step12a′ = Peel (V-G G-ƛ) (V-G (G-Λ (V-G G-ƛ)))

step12b′ : [] ⊢ T1½′ -→ T2′
step12b′ = ξ-⟪⟫ (Beta (V-⟪⟫ (V-G (G-Λ (V-G G-ƛ))) I-∀))

step23′ : [] ⊢ T2′ -→ T3′
step23′ = ξ-⟪⟫ (ξ-Λ (ξ-·-l (TyWrap (V-G G-ƛ))))

step34a′ : [] ⊢ T3′ -→ T3½′
step34a′ = ξ-⟪⟫ (ξ-Λ (Peel (V-G G-ƛ) (V-G G-ƛ)))

step34b′ : [] ⊢ T3½′ -→ T4full′
step34b′ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (Beta (V-⟪⟫ (V-G G-ƛ) I-⇒))))

-- the failing crossing is FORCED: at T3′ the only redex is that
-- application, and its argument is a value
_ : Value argY
_ = V-G G-ƛ

------------------------------------------------------------------------
-- §1.2  T0′ … T3′ type, at the program's type ∀Y. Y→ℕ
------------------------------------------------------------------------

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
           (⊢Λ (⊢· (⊢·[] (env (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])
                              sc-polyg ⊢idg)
                         (wf-var here-abst))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

-- Z's interior entry: the EXTERIOR-READ one.  "Z is Y" is not expressible
-- where Y is blocked, and unfolding is the identity at the Λ-bound Y.
_ : intOf Γ★ Θ★ ≡ xrvld (` 0) ∷ []
_ = refl

bwf-Θ★ : Γ★ ∣ intOf Γ★ Θ★ ⊢ᵇ Θ★
bwf-Θ★ = bwf↑ (wf-var here-abst)
              (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])

⊢T3′ : [] ∣ [] ⊢ T3′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T3′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
           (⊢Λ (⊢· (env bwf-Θ★
                        (sc-⇒ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
                              (sc-⇒ (sc-var hereᵒ) sc-ℕ))
                        (⊢ƛ (wf-⇒ (wf-var here-xrvld) wf-ℕ)
                            (⊢ƛ (wf-var here-xrvld)
                                (⊢· (⊢` (there here)) (⊢` here)))))
                   (⊢ƛ (wf-var here-abst) ⊢$)))

------------------------------------------------------------------------
-- §1.3  *** THE CONTRACTUM TYPES ***  The dual's conceal of Z is licensed
-- by (bwf-↓x): Z is x-revealed in the interior, and the rep ` 0 names the
-- dual's OWN rep-less reveal ↑Y:⋆, so it claims nothing.  Both faces were
-- already exactly right; only the licence was missing.
------------------------------------------------------------------------

-- the two faces, at exactly the boundary type Wrap hands the dual
face-int-E★′ : substᵗ (γᵇ dualᵛ) (` 2 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
face-int-E★′ = refl

face-ext-E★′ : substᵗ (ρᵇ dualᵛ) (` 2 ⇒ `ℕ)
             ≡ substᵗ (γᵇ Θ★) (` 0 ⇒ `ℕ)
face-ext-E★′ = refl

-- the licence, isolated: the x-lookup and the claims-nothing premise
xlic-E★′ : intOf Γ★ Θ★ ∋ 0 :=x (` 0)
xlic-E★′ = herex

star-E★′ : starOnly dualᵛ 0 (` 0) ≡ true
star-E★′ = refl

-- there is NO ordinary knowledge of Z, which is why (bwf-↓) cannot fire
no-know-E★′ : ∀ {A₁} → intOf Γ★ Θ★ ∋ 0 := A₁ → ⊥
no-know-E★′ ()

-- the dual's interior rebuilds Γ★ ON THE NOSE
rebuild-E★′ : intOf (intOf Γ★ Θ★) dualᵛ ≡ Γ★
rebuild-E★′ = refl

DualInt-E★′ : Γ★ ≼≈ intOf (intOf Γ★ Θ★) dualᵛ
DualInt-E★′ = ≼≈-refl Γ★

bwf-dualᵛ : Γz ∣ intOf Γz dualᵛ ⊢ᵇ dualᵛ
bwf-dualᵛ =
  bwf⋆ (bwf↑ wf-ℕ (bwf↓x herex refl sk-var (wf-var here-abst) bwf[]))

⊢W′ : ∀ {Γ₁ : Ctx} → Γz ∣ Γ₁ ⊢ W′ ⦂ (` 0 ⇒ `ℕ)
⊢W′ = env bwf-dualᵛ
          (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) sc-ℕ)
          (⊢ƛ (wf-var here-abst) ⊢$)

⊢T4′ : Γ★ ∣ [] ⊢ T4′ ⦂ (` 0 ⇒ `ℕ)
⊢T4′ = env bwf-Θ★ (sc-⇒ (sc-var hereᵒ) sc-ℕ)
           (⊢ƛ (wf-var here-xrvld) (⊢· ⊢W′ (⊢` here)))

⊢T4full′ : [] ∣ [] ⊢ T4full′ ⦂ `∀ (` 0 ⇒ `ℕ)
⊢T4full′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ (sc-⇒ (sc-var hereᵒ) sc-ℕ))
               (⊢Λ ⊢T4′)

------------------------------------------------------------------------
-- §2.  E★ END TO END.  Same program with the ∀-body NOT mentioning its own
-- variable (f : ∀Z. ℕ→ℕ), so the Wrap's argument is `5 : ℕ`.  It types by
-- the SAME licence — so with the x-clause, E★ needs no cnc⋆ at all.
------------------------------------------------------------------------

polyf : Ty                     -- ∀Z. ℕ→ℕ   (Z UNUSED)
polyf = `∀ (`ℕ ⇒ `ℕ)

T4 T4full : Term
T4     = (($ 5) ⟪ dualᵛ , `ℕ ⟫) ⟪ Θ★ , `ℕ ⟫
T4full = (Λ T4) ⟪ Θ1 , `∀ `ℕ ⟫

⊢T4 : Γ★ ∣ [] ⊢ T4 ⦂ `ℕ
⊢T4 = env bwf-Θ★ sc-ℕ (env bwf-dualᵛ sc-ℕ ⊢$)

⊢T4full : [] ∣ [] ⊢ T4full ⦂ `∀ `ℕ
⊢T4full = env (bwf↑ wf-ℕ bwf[]) (sc-∀ sc-ℕ) (⊢Λ ⊢T4)

-- … and UNDER DECISION 6 THE RUN CONTINUES.  T4's two boundaries have
-- BASE faces, so both are ACTIVE: they carry no type information and are
-- simply dropped (Drop$), one per step, under ξ-Λ / ξ-⟪⟫.  E★ therefore
-- terminates at `(Λ 5) ⟪ ↑X:=ℕ , ∀ℕ ⟫` — a ∀ face, INERT, so a value —
-- instead of at the three-boundary residue the old value grammar
-- accepted.  This is the base-face endpoint change the install predicts.
T4full′′ T4full′′′ : Term
T4full′′  = (Λ (($ 5) ⟪ Θ★ , `ℕ ⟫)) ⟪ Θ1 , `∀ `ℕ ⟫
T4full′′′ = (Λ ($ 5)) ⟪ Θ1 , `∀ `ℕ ⟫

drop-T4-inner : [] ⊢ T4full -→ T4full′′
drop-T4-inner = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ Drop$))

drop-T4-outer : [] ⊢ T4full′′ -→ T4full′′′
drop-T4-outer = ξ-⟪⟫ (ξ-Λ Drop$)

⊢T4full′′′ : [] ∣ [] ⊢ T4full′′′ ⦂ `∀ `ℕ
⊢T4full′′′ = env (bwf↑ wf-ℕ bwf[]) (sc-∀ sc-ℕ) (⊢Λ ⊢$)

-- … and THAT is the value of the program's type: E★ terminates
val-T4full′′′ : Value T4full′′′
val-T4full′′′ = V-⟪⟫ (V-G (G-Λ V-$)) I-∀

-- the old residue is NOT a value any more — a base face is never inert
¬val-T4full : ¬ Value T4full
¬val-T4full (V-⟪⟫ (V-G (G-Λ (V-⟪⟫ _ ()))) _)

------------------------------------------------------------------------
-- §3.  Pn — THE PRICE OF DROPPING THE AMBIENT UNFOLD RETRY.
--
-- Γn = Y:=ℕ , X:=ℕ with ↑Z:=Y , ↓X:=ℕ.  The interior DROPS Y, so the raw
-- reading of Z's rep is blocked; the probes' middle step retried at
-- unfoldᵉ Γn (` 0) = ℕ and got genuine knowledge Z:=ℕ.  That step is gone
-- (strong.Boundary's flagged deviation: it breaks BOTH ⊢renameᵀ's ⟦⟧-ren
-- and ⊢retag's interior monotonicity), so Z gets the exterior-read entry
-- and its dual's conceal is licensed by NEITHER clause — the ONE gauntlet
-- item this install loses, and it lands in DualCnc≈.
------------------------------------------------------------------------

_ : intOf Γn Θn ≡ xrvld (` 0) ∷ []
_ = refl

dualⁿ : BCtx
dualⁿ = rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []

_ : dualᴳ Γn Θn ≡ dualⁿ
_ = refl

-- (bwf-↓) cannot fire: the interior has no ORDINARY knowledge of Z …
¬know-Pn : ∀ {A₁} → intOf Γn Θn ∋ 0 := A₁ → ⊥
¬know-Pn ()

-- … and (bwf-↓x) cannot either: the rep ` 0 names the dual's slot 0, which
-- is a REP-CARRYING reveal ↑Y:=ℕ, so it claims something.
¬star-Pn : ¬ (starOnly dualⁿ 0 (` 0) ≡ true)
¬star-Pn ()

-- the x-lookup itself IS there — it is only the claims-nothing half that
-- fails, which is exactly DualLicenseProbe §4.5's xlic-Pnⁿ vs ¬abs-Pnⁿ
xlic-Pn : intOf Γn Θn ∋ 0 :=x (` 0)
xlic-Pn = herex

------------------------------------------------------------------------
-- §4.  DUAL OF DUAL, on E★′'s shapes.  The ⋆-reveal duals to cnc⋆ (this is
-- where cnc⋆ is indispensable — there is no rep to keep), the copied
-- reveal to an ordinary conceal, and the reveal of the concealed Z slot
-- re-reveals its rep.  The round trip is EXACT.
------------------------------------------------------------------------

dd : BCtx
dd = rvl (` 0) ∷ cnc⋆ 0 ∷ cnc 1 `ℕ ∷ []

_ : dualᴳ Γz dualᵛ ≡ dd
_ = refl

_ : intOf Γ★ dd ≡ Γz                 -- the round trip
_ = refl

⊢dd : Γ★ ∣ intOf Γ★ dd ⊢ᵇ dd
⊢dd = bwf↑ (wf-var here-abst)
           (bwf⋆↓ here-abst
             (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))

-- and the ⋆-concealed slot is UNNAMEABLE, which is what keeps cnc⋆ honest
_ : baseS dd Γ★ ≡ ok ∷ blk ∷ ok ∷ []
_ = refl

¬Scoped-dd : ¬ Scoped (baseS dd Γ★) (` 1)
¬Scoped-dd (sc-var (thereᵒ ()))

------------------------------------------------------------------------
-- §5.  Pc's CHAINED-COPY SITE.  Γq = W:=Y , Y:=ℕ , X:=ℕ is reachable
-- (TyBeta turns a Λ-bound Y into W:=Y without renaming) and Θq = ↓X:=ℕ
-- drops all three.  W's entry is the CHAIN "W is Y", and Θq drops Y too, so
-- the RAW copy's guard refuses it — the knowledge used to be LOST to rvl⋆.
-- The SECOND-CHANCE copy retries at the rep unfolded in its own tail, which
-- collapses the chain, so all three slots come back with knowledge and the
-- rebuild is ONE UNFOLDING away from Γq — which _≼≈_ absorbs.
------------------------------------------------------------------------

Γq Γq′ : TCtx
Γq  = rvld (` 0) ∷ rvld `ℕ ∷ rvld `ℕ ∷ []
Γq′ = rvld `ℕ   ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

Θq : BCtx
Θq = cnc 2 `ℕ ∷ []

_ : intOf Γq Θq ≡ []
_ = refl

-- the raw guard refuses W's chained rep …
_ : dfree 0 2 (` 0) ≡ false
_ = refl

-- … and the second chance takes it, at the collapsed rep ℕ
_ : unfEnt Γq 0 (` 0) ≡ `ℕ
_ = refl

_ : dualᴳ Γq Θq ≡ rvl `ℕ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

_ : intOf (intOf Γq Θq) (dualᴳ Γq Θq) ≡ Γq′
_ = refl

-- THE CONTEXT LAW.  Syntactic _≼_ ordered Γq and Γq′ in neither direction;
-- _≼≈_ orders them, because the difference is exactly one unfolding.
DualInt-Γq : Γq ≼≈ intOf (intOf Γq Θq) (dualᴳ Γq Θq)
DualInt-Γq = ≼≈rvld (≼≈rvld (≼≈rvld ≼≈[] ≈-refl) ≈-refl) (≈unf refl)

⊢dualᴳ-Γq : intOf Γq Θq ∣ intOf (intOf Γq Θq) (dualᴳ Γq Θq)
            ⊢ᵇ dualᴳ Γq Θq
⊢dualᴳ-Γq = bwf↑ wf-ℕ (bwf↑ wf-ℕ (bwf↑ wf-ℕ bwf[]))

-- THE SITE ≈ WAS INTRODUCED FOR: the argument's ↓W:=Y conceal, retyped in
-- the rebuilt context.  In Γq the conceal is licensed on the nose; in Γq′
-- the knowledge for W is the unfolded ℕ while the read-back is still the
-- raw variable ` 1, so the SYNTACTIC premise fails and only ≈ carries it.
argW : Term
argW = (($ 3) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ cnc 0 (` 0) ∷ [] , ` 0 ⟫

⊢argW : Γq ∣ [] ⊢ argW ⦂ ` 0
⊢argW =
  env (bwf↓ here (≡→≈ refl) (wf-var here-rvld) bwf[])
      (sc-var hereᵒ)
      (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

¬Reversal-argW′ : ¬ (Reversal (cnc 0 (` 0) ∷ []) 0 (` 0) `ℕ)
¬Reversal-argW′ ()

Reversal≈-argW′ : Reversal≈ Γq′ (cnc 0 (` 0) ∷ []) 0 (` 0) `ℕ
Reversal≈-argW′ = ≈unf refl

-- … and ⊢retag≈ does it wholesale, which is what Wrap's preservation case
-- consumes
⊢argW-rebuilt : Γq′ ∣ [] ⊢ argW ⦂ ` 0
⊢argW-rebuilt = ⊢retag≈ DualInt-Γq ⊢argW

------------------------------------------------------------------------
-- §6.  SOUNDNESS.  The relaxation must reach exactly as far as the
-- exterior's knowledge, and no further.
------------------------------------------------------------------------

-- bad / bad₂ stay refuted (strong.Boundary's ¬⊢bad / ¬Reversal≈-bad₂), and
-- the x-clause cannot fire at either, because the exterior carries ORDINARY
-- knowledge there rather than an x-mark
¬⊢bad-here : ¬ ([] ∣ [] ⊢ bad ⦂ ∀ZZ)
¬⊢bad-here = ¬⊢bad

¬xlic-bad : ∀ {A₁} → (rvld ∀ZZ ∷ []) ∋ 0 :=x A₁ → ⊥
¬xlic-bad ()

¬xlic-bad₂ : ∀ {A₁} → Γb ∋ 0 :=x A₁ → ⊥
¬xlic-bad₂ ()

-- the NEAR-bad is ADMITTED (W really is ℕ, by the other route) …
near-bad-ok : Reversal≈ Γnb Θnb 0 `ℕ (` 0)
near-bad-ok = Reversal≈-near-bad

-- … and the FAR-bad is refused
far-bad-no : ¬ (Reversal≈ Γnb (cnc 0 ∀ZZ ∷ []) 0 ∀ZZ (` 0))
far-bad-no = ¬Reversal≈-far-bad

-- THE ⊢3n-adv ADVERSARY, AND THE §5(ii) GAUNTLET ITEM.  It reuses E★′'s own
-- legitimately-minted x-entry with a boundary that is NOT the dual, and it
-- is REFUTED.  What refutes it is the claims-nothing premise alone: its
-- conceal rep IS the recorded one, so both the syntactic rep comparison and
-- the ≈Δ̄ one HOLD for it.  VERDICT: refuted under ≈; the ≈ addition is not
-- what refutes it, so §5(ii)'s expectation is confirmed.
¬⊢adv-here : ¬ (Γz ∣ [] ⊢ adv ⦂ ` 0)
¬⊢adv-here = ¬⊢adv

adv-rep-holds≈ : (` 0) ≈Δ̄⟨ Γz ⟩ (` 0)
adv-rep-holds≈ = adv-rep-match≈

adv-claims-something : ¬ (starOnly Ξadv 0 (` 0) ≡ true)
adv-claims-something = ¬starOnly-adv

-- a conceal of a PLAIN Λ-bound abstract variable stays unlicensed: the
-- x-lookup is what discriminates (bwf1-garbage's shape)
¬x-plain : ∀ {A₁} → (abst ∷ []) ∋ 0 :=x A₁ → ⊥
¬x-plain = ¬x-plain-abst

------------------------------------------------------------------------
-- §7.  RENAMING.
--
-- (a) A transport instance that TOUCHES an xrvld entry: weakening E★′'s
--     dual-wrapped argument by a fresh Λ-bound slot.  The exterior Γz's
--     x-entry rides the transport (hx-suc), and its rep is carried across
--     verbatim — a weakening does not rewrite stored entries.
------------------------------------------------------------------------

h-suc : ∀ {Δ₁ : TCtx} {X} → Δ₁ ∋tv X → (abst ∷ Δ₁) ∋tv suc X
h-suc p = skip-abst p

⊢W′-weakened :
  (abst ∷ Γz) ∣ map (renameᵗ suc) [] ⊢ renameᵀ suc W′ ⦂ renameᵗ suc (` 0 ⇒ `ℕ)
⊢W′-weakened = ⊢renameᵀ h-suc Mono-suc hk-suc hx-suc (⊢W′ {Γ₁ = []})

-- the renamed wrapper, computed: the ⋆-conceal's INDEX moves and nothing
-- else does, while the exterior's x-entry stays put
_ : renameᵀ suc W′ ≡ argY ⟪ rvl⋆ ∷ rvl `ℕ ∷ cnc 1 (` 0) ∷ []
                          , (` 3 ⇒ `ℕ) ⟫
_ = refl

------------------------------------------------------------------------
-- (b) WHY (bwf-↓x)'s COMPARISON IS NEITHER ≡ NOR ≈Δ̄
--     (notes/DualLicenseDesign.md §5).  Weaken Γ★ by a fresh Λ-bound V.
--     The renaming ⊢renameᵀ hands the sealed body is ρ₁ = intRen suc Θ★,
--     which is the IDENTITY on the dual's frame — so the TERM's conceal rep
--     is FROZEN at ` 0 while the CONTEXT's x-rep moves to ` 1.  The
--     syntactic comparison fails, and so does the ≈Δ̄ one: in the renamed
--     interior ` 0 is the x-revealed Z and ` 1 is out of range, so their
--     unfoldings are themselves and differ.  Ruling (ii) therefore does NOT
--     make EITHER of those forms ⊢renameᵀ-stable; §8 is the form that
--     survives, and it survives exactly this instance.
------------------------------------------------------------------------

Δw : TCtx
Δw = abst ∷ Γ★

ρ₁ : ℕ → ℕ
ρ₁ = intRen suc Θ★

Θ★w : BCtx
Θ★w = renᴮ suc ρ₁ Θ★

_ : Θ★w ≡ rvl (` 1) ∷ cnc 2 `ℕ ∷ []
_ = refl

_ : intOf Δw Θ★w ≡ xrvld (` 1) ∷ []       -- the x-rep moved by ρ = suc …
_ = refl

_ : renᴮ ρ₁ (intRen ρ₁ dualᵛ) dualᵛ ≡ dualᵛ   -- … the term's did not
_ = refl

-- the SYNTACTIC comparison fails …
¬x-rep-match-ren : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
¬x-rep-match-ren ()

-- … and so does the ≈Δ̄ one, at the renamed interior
¬x-rep-match-ren≈ : ¬ ((` 0) ≈Δ̄⟨ intOf Δw Θ★w ⟩ (` 1))
¬x-rep-match-ren≈ (≈unf ())

-- what DOES hold, and is what the rule asks for: the x-LOOKUP at the moved
-- slot, and the claims-nothing premise (which mentions no context at all)
xlic-ren-ok : intOf Δw Θ★w ∋ 0 :=x (` 1)
xlic-ren-ok = herex

star-ren-ok : starOnly (renᴮ ρ₁ (intRen ρ₁ dualᵛ) dualᵛ) 0 (` 0) ≡ true
star-ren-ok = refl

------------------------------------------------------------------------
-- §8.  THE SkelEq REPAIR (notes/DECISIONS.md's "D1 PROBE VERDICT — … the
-- SkelEq repair"; the reference probe is notes/D1Probe.agda §7).
--
-- (bwf-↓x) now carries a third premise: SkelEq A A′, "the conceal's rep has
-- the same SKELETON as the recorded x-rep" — the constructor tree, with
-- VARIABLE POSITIONS IDENTIFIED.  Four things had to be true of it, and all
-- four are checked below:
--
--   §8.1  it is DISCHARGED AT BIRTH by a theorem — at every dual's birth the
--         two reps are SYNTACTICALLY equal (xrep-stored / dual-cnc-skel), so
--         the only rule that mints x-conceals pays nothing;
--   §8.2  it SURVIVES §7b's weakening, the very instance that refutes ≡ and
--         ≈Δ̄ — and by the hypothesis-free stability theorem, not by
--         computation;
--   §8.3  it REFUSES the soundness hole the comparison-free licence had: a
--         CLOSED rep at an x-slot, which starOnly admits;
--   §8.4  the ⊢3n-adv adversary still PASSES it, so §6's refutation is
--         still carried by starOnly alone — the repair is orthogonal.
------------------------------------------------------------------------

-- §8.1  BIRTH.  E★′'s dual conceals Z at the rep ` 0 and the interior's
-- x-entry records ` 0 — not by coincidence: the x-lookup inside a reveal
-- block RETURNS the stored reveal rep, which is the rep cncOfRevs hands the
-- dual's conceal.
xrep-stored-E★′ : (` 0) ≡ ρᵇ Θ★ 0
xrep-stored-E★′ = xrep-stored Θ★ 0 Θ★ 0 (s≤s z≤n) xlic-E★′

skel-birth-E★′ : SkelEq (ρᵇ Θ★ 0) (` 0)
skel-birth-E★′ = dual-cnc-skel {Δ₀ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

-- … which is exactly the premise the live bwf-dualᵛ now supplies
skel-live-E★′ : SkelEq (` 0) (` 0)
skel-live-E★′ = sk-var

-- and the whole contractum still types through it (§1.3, re-run)
⊢T4′-still : Γ★ ∣ [] ⊢ T4′ ⦂ (` 0 ⇒ `ℕ)
⊢T4′-still = ⊢T4′

------------------------------------------------------------------------
-- §8.2  THE WEAKENING.  §7b's pair — the frozen conceal rep ` 0 against the
-- moved x-rep ` 1 — is still LICENSED, because skeletons identify variable
-- positions.  The witness comes from skel-ren applied to the two INDEPENDENT
-- renamings (the interior one, which absorbs the shift, and the exterior
-- suc): no Mono, no transport hypothesis, no absorption side condition.
------------------------------------------------------------------------

skel-post-ren : SkelEq (renameᵗ (intRen ρ₁ dualᵛ) (` 0)) (renameᵗ suc (` 0))
skel-post-ren = skel-ren (intRen ρ₁ dualᵛ) suc sk-var

skel-ok-ren : SkelEq (` 0) (` 1)
skel-ok-ren = skel-post-ren

-- the same pair, in the two forms that FAIL there (cited from §7b)
skel-vs-≡ : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
skel-vs-≡ = ¬x-rep-match-ren

skel-vs-≈ : ¬ ((` 0) ≈Δ̄⟨ intOf Δw Θ★w ⟩ (` 1))
skel-vs-≈ = ¬x-rep-match-ren≈

-- … and §7a's live transport instance is unchanged: hx-suc now carries the
-- SkelEq witness too (skel-refl — a weakening copies the entry verbatim),
-- so ⊢renameᵀ's strengthened hypothesis is discharged by the same term
⊢W′-weakened-still :
  (abst ∷ Γz) ∣ map (renameᵗ suc) [] ⊢ renameᵀ suc W′ ⦂ renameᵗ suc (` 0 ⇒ `ℕ)
⊢W′-weakened-still = ⊢renameᵀ h-suc Mono-suc hk-suc SkelX-suc (⊢W′ {Γ₁ = []})

------------------------------------------------------------------------
-- §8.3  THE HOLE, CLOSED.  Θg conceals E★′'s own x-slot at the CLOSED rep
-- ℕ.  starOnly ADMITS it (starOnly Θ d `ℕ = true), so the comparison-free
-- licence typed a ℕ literal at the Λ-BOUND Y — and, one ⊢retag≈ away, at a
-- slot the exterior knows to be ∀Z.Z→Z, which is `bad`'s own configuration.
-- Both are now REFUTED, by the skeleton premise alone.
------------------------------------------------------------------------

starOnly-does-not-refuse : starOnly Θg 0 `ℕ ≡ true
starOnly-does-not-refuse = starOnly-ground

skel-does-refuse : ¬ (SkelEq `ℕ (` 0))
skel-does-refuse = ¬skel-ground

-- the inner half and the two towers (strong.Boundary's refutations, cited)
¬⊢gnd-here : ¬ (Γz ∣ [] ⊢ ($ 7) ⟪ Θg , ` 0 ⟫ ⦂ ` 0)
¬⊢gnd-here = ¬⊢gnd

¬⊢Tg-here : ¬ (Γ₈ ∣ [] ⊢ Tg ⦂ ` 0)
¬⊢Tg-here = ¬⊢Tg

¬⊢Tbad-here : ¬ (Δbad ∣ [] ⊢ Tg ⦂ ` 0)
¬⊢Tbad-here = ¬⊢Tbad

-- the same tower on E★′'s OWN boundary ordering (D1Probe's ⊢Tg verbatim),
-- so the refutation is not an artefact of Θ₈'s entry order
Tg★ : Term
Tg★ = (($ 7) ⟪ Θg , ` 0 ⟫) ⟪ Θ★ , ` 0 ⟫

¬⊢Tg★ : ¬ (Γ★ ∣ [] ⊢ Tg★ ⦂ ` 0)
¬⊢Tg★ (env _ _ (env (bwf↓  () _ _ _) _ _))
¬⊢Tg★ (env _ _ (env (bwf↓x herex _ () _ _) _ _))

-- REACHABILITY, for the record: ⊢retag≈ along Γ★ ≼≈ Γ𝔹 is the transport
-- TyBeta performs when the Λ is instantiated, and it carried D1Probe's ⊢Tg
-- into a context that KNOWS Y.  With the tower refuted at BOTH ends there is
-- nothing left to transport.
Γ𝔹 : TCtx
Γ𝔹 = rvld `𝔹 ∷ rvld `ℕ ∷ []

Γ★≼Γ𝔹 : Γ★ ≼≈ Γ𝔹
Γ★≼Γ𝔹 = ≼≈abst (≼≈rvld ≼≈[] ≈-refl)

¬⊢Tg★-instantiated : ¬ (Γ𝔹 ∣ [] ⊢ Tg★ ⦂ ` 0)
¬⊢Tg★-instantiated (env _ _ (env (bwf↓  () _ _ _) _ _))
¬⊢Tg★-instantiated (env _ _ (env (bwf↓x herex _ () _ _) _ _))

------------------------------------------------------------------------
-- §8.4  ORTHOGONALITY.  The ⊢3n-adv adversary's conceal rep IS the recorded
-- one, so it passes SkelEq exactly as it passes ≡ and ≈Δ̄ (§6).  Its
-- refutation is still carried entirely by claims-nothing — so the repair
-- adds a refutation and removes none.
------------------------------------------------------------------------

adv-passes-skel : SkelEq (` 0) (` 0)
adv-passes-skel = adv-rep-skel

adv-still-refuted : ¬ (Γz ∣ [] ⊢ adv ⦂ ` 0)
adv-still-refuted = ¬⊢adv

adv-still-by-starOnly : ¬ (starOnly Ξadv 0 (` 0) ≡ true)
adv-still-by-starOnly = ¬starOnly-adv

-- and the ⊢3s-alias residue and a COMPOUND blocked rep are still admitted,
-- so the premise is not over-restrictive (a "the rep must BE the recorded
-- variable" premise would have refused the latter)
skel-alias : SkelEq (` 0) (` 0)
skel-alias = sk-var

skel-compound-ok : SkelEq (` 0 ⇒ `ℕ) (` 1 ⇒ `ℕ)
skel-compound-ok = skel-compound

------------------------------------------------------------------------
-- §9.  THE COLLAPSE RULES (Decision 3, RE-RULED BY DECISION 6 —
-- ACTIVE/INERT, 2026-09-04).  Merge now fires only at an ACTIVE outer
-- face (a reveal variable) around an INERT inner one, and Drop∅ has been
-- replaced by Drop$ at a BASE face; §9a–§9e are re-checked under that
-- restriction.  Where a nesting's faces are ⇒ / ∀ it is now a VALUE and
-- no longer merges at all (§9c) — its ⊕ arithmetic is kept as the record
-- of what a merge WOULD compute.  The suite is in five parts:
--
--   §9a  the cancel pair, end to end: Merge then Drop$ to the bare value;
--   §9b  E★'s own continuation tower merged — an X-PAIR cancel, licensed
--        by (bwf-↓x), with the two reps agreeing by xrep-stored;
--   §9c  the Example-3-shaped tower merged twice, and the REFUTATION of the
--        mrg₂ (TOPLAS "keep the outer type") form on it;
--   §9d  THE TWO LIMITS of the landed ⊕: the external-face equation is a
--        rule PREMISE and not a lemma (an ⇒-faced counterexample), and the
--        scope premise can fail on an alias cancel.  Both come with the
--        alternative merged boundary that DOES work, so the obstruction is
--        ⊕'s eager push-out and not Merge itself;
--   §9l  THE DECISION-6 RESIDUE and a COUNTEREXAMPLE to it: MergeOK is
--        not derivable at every well-typed active reveal-variable
--        nesting, and the sole failing component is ⊕-γ's side condition;
--   §9e  the TOPLAS three-agent adversary re-checked against the live ⊕:
--        their shape does not reach our cancel clause (nor, under ⊕-γ's
--        side condition, our Merge at all), the appended merge types with
--        both authorities kept — and there the RIGHT B₂′ is the mrg₂ one,
--        which is the other half of §9c's refutation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §9a.  THE CANCEL PAIR.  (7 ⟪ ↓X:=ℕ ⟫) ⟪ ↑X:=ℕ ⟫ --Merge--→ 7 ⟪ ∅ , ℕ ⟫
-- --Drop$--→ 7.  Cited from strong.BReduction, where the rule's worked
-- example lives (PLAN §1's Method).  Under Decision 6 the classification
-- is what LICENSES both steps: the inner face ` 0 is INERT (Θ1c reveals
-- nothing), the outer face ` 0 is ACTIVE (0 < revs Θ2c = 1), and the
-- contractum's face ℕ is active too — so the redex is not a value, the
-- merge is its unique step, and the empty-boundary residue is dropped by
-- the BASE-face rule rather than by a rule of its own.
------------------------------------------------------------------------

merge-c : [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ -→ ($ 7) ⟪ [] , `ℕ ⟫
merge-c = Merge V-$ (I-var z≤n) (A-var (s≤s z≤n)) ok-c

drop-c : [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ -→ $ 7
drop-c = Drop$

-- neither the redex nor the residue is a value: Decision 6's whole point
¬val-c : ¬ Value ((($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫)
¬val-c (V-⟪⟫ _ (I-var ()))

-- … and each step is the UNIQUE one, by det
merge-c-uniq : ∀ {M′} → [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ -→ M′
             → M′ ≡ ($ 7) ⟪ [] , `ℕ ⟫
merge-c-uniq st = det st merge-c

types-c : [] ∣ [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ ⦂ `ℕ
types-c = ⊢redex-c

types-c′ : [] ∣ [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ ⦂ `ℕ
types-c′ = ⊢contractum-c

types-c″ : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
types-c″ = ⊢final-c

-- *** CANCEL-AGREE FOR AN ORDINARY PAIR ***, through the GENERAL lemma
-- (strong.BReduction's rep-stored / cancel-agree — the ≡-analogue of
-- DualDef's xrep-stored): the interior's knowledge at a reveal slot IS the
-- reading of that reveal's STORED rep …
cancel-agree-gen : `ℕ ≡ dnT 1 (rawRead Θ2c (ρᵇ Θ2c 0))
cancel-agree-gen = cancel-agree {Δ₀ = []} Θ2c 0 (s≤s z≤n) here

-- … and the deleted conceal's own (bwf-↓) premise ties ITS rep to that same
-- knowledge, read BACK OUT through the boundary.  Between them, the rep the
-- cancel keeps and the rep the deleted reveal carried are one type.
cancel-rev-c : Reversal≈ (intOf [] Θ2c) Θ1c 0 `ℕ `ℕ
cancel-rev-c = ≡→≈ refl

cancel-agree-c : outRead Θ1c `ℕ ≡ upRep 0 `ℕ
cancel-agree-c = refl

------------------------------------------------------------------------
-- §9b.  E★'s CONTINUATION TOWER — THE X-PAIR CANCEL.
--
-- T4 = (5 ⟪ Θᵈ , ℕ ⟫) ⟪ ↑Z:=Y , ↓X:=ℕ , ℕ ⟫  (§2) is a nested wrapper, and
-- the cancelling pair is Θᵈ's ↓Z:=Y — the conceal the whole x-licence
-- exists for — against Θ★'s ↑Z:=Y.  The composite keeps the dual's ↑Y:⋆
-- and ↑X:=ℕ and Θ★'s ↓X:=ℕ; both faces are ℕ, so the merge is exact.
--
-- UNDER DECISION 6 THE MERGE IS NOT THE STEP TAKEN HERE.  BOTH faces are
-- the BASE type ℕ, hence ACTIVE, so neither wrapper is a value and the
-- INNER one is dropped first (Drop$), then the outer: the tower runs to
-- the bare 5 in two steps, not one.  The MERGE PACKAGE IS KEPT — ok-★ is
-- still fully discharged and ⊢merged-★ still types — because it is the
-- x-pair cancel evidence this section exists for; what changed is only
-- which rule fires, and the two routes agree on the answer (drop-★-agree).
------------------------------------------------------------------------

Θmg : BCtx
Θmg = dualᵛ ⊕ Θ★

_ : Θmg ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 1 `ℕ ∷ []
_ = refl

-- the interiors compose ON THE NOSE here (the dual's rebuild is exact)
_ : intOf Γ★ Θmg ≡ Γ★
_ = refl

bwf-Θmg : Γ★ ∣ intOf Γ★ Θmg ⊢ᵇ Θmg
bwf-Θmg =
  bwf⋆ (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))

ok-★ : MergeOK Γ★ dualᵛ Θ★ `ℕ `ℕ
ok-★ = s≤s z≤n , bwf-Θmg , sc-ℕ , ≼≈-refl Γ★ , refl

-- the merged wrapper still TYPES at the tower's own type: the composite
-- and its faces are right, it is simply not what the machine computes
⊢merged-★ : Γ★ ∣ [] ⊢ ($ 5) ⟪ Θmg , `ℕ ⟫ ⦂ `ℕ
⊢merged-★ = env bwf-Θmg sc-ℕ ⊢$

-- what the machine DOES: two base-face drops, to the bare 5
drop-★-inner : Γ★ ⊢ T4 -→ ($ 5) ⟪ Θ★ , `ℕ ⟫
drop-★-inner = ξ-⟪⟫ Drop$

drop-★-outer : Γ★ ⊢ ($ 5) ⟪ Θ★ , `ℕ ⟫ -→ $ 5
drop-★-outer = Drop$

-- and the merged route reaches the same answer, one more drop away
drop-★-agree : Γ★ ⊢ ($ 5) ⟪ Θmg , `ℕ ⟫ -→ $ 5
drop-★-agree = Drop$

-- *** CANCEL-AGREE FOR THE X-PAIR ***  the interior's x-entry at Θ★'s
-- reveal slot records exactly the stored rep (xrep-stored), so the two reps
-- of the cancelling pair are SYNTACTICALLY EQUAL at the dual's birth, and
-- the skeleton premise the licence carries is free (dual-cnc-skel).
cancel-agree-x : (` 0) ≡ ρᵇ Θ★ 0
cancel-agree-x = xrep-stored Θ★ 0 Θ★ 0 (s≤s z≤n) xlic-E★′

cancel-skel-x : SkelEq (ρᵇ Θ★ 0) (` 0)
cancel-skel-x = dual-cnc-skel {Δ₀ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

-- … and the whole tower under the outermost ↑X:=ℕ steps the same way, by
-- ξ-Λ / ξ-⟪⟫ carrying the index into the interior (this IS §2's
-- drop-T4-inner, restated at Θmg's section)
drop-★full : [] ⊢ T4full -→ (Λ (($ 5) ⟪ Θ★ , `ℕ ⟫)) ⟪ Θ1 , `∀ `ℕ ⟫
drop-★full = ξ-⟪⟫ (ξ-Λ drop-★-inner)

------------------------------------------------------------------------
-- §9c.  THE EXAMPLE-3-SHAPED TOWER (strong.BReduction's worked example
-- (c)) — and the REFUTATION of the mrg₂ form.
--
-- UNDER DECISION 6 THIS TOWER DOES NOT STEP AT ALL.  Every face here is
-- ⇒-shaped, hence INERT, so the tower is a VALUE at rest and its
-- boundaries are consumed one layer per application by Peel, never
-- merged.  The ⊕ arithmetic and the two fully discharged MergeOK
-- packages are kept as the record of what a merge WOULD compute — and
-- the mrg₂ refutation below is unaffected, since it is a statement about
-- ⊕ and not about any rule.
------------------------------------------------------------------------

tower-types : Δtw ∣ []
  ⊢ ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  ⦂ (` 0 ⇒ ` 0)
tower-types = ⊢tower

-- the tower is a VALUE, and therefore takes no step whatever
tower-value : Value
  (((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫)
tower-value = val-tower

tower-stuck : ∀ {M′} → Δtw ⊢
  ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  -→ M′ → ⊥
tower-stuck = tower-¬-→

-- the merge packages are still fully discharged, and the twice-merged
-- boundary still types the value at the tower's own type
tower-ok₁ : MergeOK Ψtw3 Θtw1 Θtw2 (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
tower-ok₁ = ok-tw1

tower-ok₂ : MergeOK Δtw (Θtw1 ⊕ Θtw2) Θtw3 (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
tower-ok₂ = ok-tw2

tower-merged : Δtw ∣ [] ⊢ Vtw ⟪ Θtw⊕ , ` 0 ⇒ ` 0 ⟫ ⦂ (` 0 ⇒ ` 0)
tower-merged = ⊢tower″

-- *** THE mrg₂ FORM IS REFUTED HERE. ***  "Keep the OUTER boundary type"
-- transports B₂ = Z₂→Z₂ to the composite's Z₂ SLOT — but the body is typed
-- at Z₃, the composite's own first reveal, and the two differ (they are
-- ≈Δ̄-equal in the merged interior, which typing does not see).  This is
-- why the landed B₂′ is the B₁-pushed-out form mrgB.
_ : substᵗ (mrg₂ Θtw1 Θtw2) (` 0 ⇒ ` 0) ≡ (` 1 ⇒ ` 1)
_ = refl

¬γ-mrg₂-tower :
  ¬ (substᵗ (γᵇ (Θtw1 ⊕ Θtw2)) (substᵗ (mrg₂ Θtw1 Θtw2) (` 0 ⇒ ` 0))
     ≡ substᵗ (γᵇ Θtw1) (` 0 ⇒ ` 0))
¬γ-mrg₂-tower ()

-- the landed form, by contrast, is exact on both faces here
γ-mrgB-tower : substᵗ (γᵇ (Θtw1 ⊕ Θtw2)) (mrgB Θtw1 Θtw2 (` 0 ⇒ ` 0))
             ≡ substᵗ (γᵇ Θtw1) (` 0 ⇒ ` 0)
γ-mrgB-tower = refl

ρ-mrgB-tower : substᵗ (ρᵇ (Θtw1 ⊕ Θtw2)) (mrgB Θtw1 Θtw2 (` 0 ⇒ ` 0))
             ≡ substᵗ (ρᵇ Θtw2) (` 0 ⇒ ` 0)
ρ-mrgB-tower = refl

------------------------------------------------------------------------
-- §9d.  THE TWO LIMITS OF THE LANDED ⊕.
--
-- (i) THE EXTERNAL FACE IS A PREMISE, NOT A LEMMA.  Δcx = X:=ℕ; the outer
-- boundary CONCEALS X at ℕ and its boundary type NAMES X (X⇒ℕ); the inner
-- one re-reveals a fresh W at that same ℕ (W⇒ℕ).  Everything type-checks,
-- and the term is an ⇒-faced nested wrapper — a NestedApp redex.  But ⊕
-- pushes the inner reveal's rep OUT through Θ₂, which resolves it to ℕ, so
-- the composite exports ℕ⇒ℕ where the redex had X⇒ℕ: the merge would DROP
-- X's abstraction (TOPLAS's authority warning, in our syntax).  The
-- boundary that DOES work keeps the abstract witness — rvl (` 0), i.e. the
-- reveal re-abstracted AT X — so the obstruction is ⊕'s eager push-out,
-- not Merge.
------------------------------------------------------------------------

Δcx : TCtx
Δcx = rvld `ℕ ∷ []

Θcx2 Θcx1 : BCtx
Θcx2 = cnc 0 `ℕ ∷ []                   -- ↓X:=ℕ  (the OUTER boundary)
Θcx1 = rvl `ℕ ∷ []                     -- ↑W:=ℕ  (the INNER one)

Vcx : Term
Vcx = ƛ ` 0 ∙ ($ 3)

⊢redex-cx : Δcx ∣ []
  ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫ ⦂ (` 0 ⇒ `ℕ)
⊢redex-cx =
  env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[])
      (sc-⇒ (sc-var hereᵒ) sc-ℕ)
      (env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) sc-ℕ)
           (⊢ƛ (wf-var here-rvld) ⊢$))

_ : Θcx1 ⊕ Θcx2 ≡ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

_ : mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
_ = refl

-- the composite's external face is ℕ⇒ℕ, the redex's type is X⇒ℕ
¬ext-cx : ¬ (substᵗ (ρᵇ (Θcx1 ⊕ Θcx2)) (mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ))
             ≡ substᵗ (ρᵇ Θcx2) (` 0 ⇒ `ℕ))
¬ext-cx ()

-- … so the merged wrapper is NOT typable at the redex's type: MergeOK's
-- last component is genuinely load-bearing
¬⊢merged-cx : ¬ (Δcx ∣ []
  ⊢ Vcx ⟪ Θcx1 ⊕ Θcx2 , mrgB Θcx1 Θcx2 (` 0 ⇒ `ℕ) ⟫ ⦂ (` 0 ⇒ `ℕ))
¬⊢merged-cx ⊢M with env-ty ⊢M
¬⊢merged-cx ⊢M | ()

-- THE REPAIR: a merged boundary whose reveal keeps the abstract witness.
-- Both faces are then exactly the redex's, and its interior is the nested
-- one on the nose.
Θcx′ : BCtx
Θcx′ = rvl (` 0) ∷ cnc 0 `ℕ ∷ []

_ : intOf Δcx Θcx′ ≡ intOf (intOf Δcx Θcx2) Θcx1
_ = refl

_ : substᵗ (γᵇ Θcx′) (` 0 ⇒ `ℕ) ≡ substᵗ (γᵇ Θcx1) (` 0 ⇒ `ℕ)
_ = refl

_ : substᵗ (ρᵇ Θcx′) (` 0 ⇒ `ℕ) ≡ substᵗ (ρᵇ Θcx2) (` 0 ⇒ `ℕ)
_ = refl

⊢repair-cx : Δcx ∣ [] ⊢ Vcx ⟪ Θcx′ , ` 0 ⇒ `ℕ ⟫ ⦂ (` 0 ⇒ `ℕ)
⊢repair-cx =
  env (bwf↑ (wf-var here-rvld) (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) sc-ℕ)
      (⊢ƛ (wf-var here-rvld) ⊢$)

------------------------------------------------------------------------
-- (ii) THE SCOPE PREMISE CAN FAIL ON AN ALIAS CANCEL.  Take E★′'s admitted
-- alias residue (strong.Boundary's Ξalias: ↑V:⋆ , ↓Z:=V) as the INNER
-- boundary over Θ★'s interior, with a boundary type that NAMES the aliased
-- slot.  The cancel deletes ↓Z:=V against Θ★'s ↑Z:=Y and leaves the
-- rep-less ↑V:⋆ — whose baseS slot is `blk`, so the merged boundary type
-- (which is that very slot) is UNSCOPED.  Again the repair exists: keep
-- Θ★'s reveal instead of the alias's ⋆-reveal.
------------------------------------------------------------------------

Θal : BCtx
Θal = Ξalias                           -- ↑V:⋆ , ↓Z:=V  over Θ★'s interior

Val : Term
Val = ƛ ` 0 ∙ ($ 5)

⊢redex-al : Γ★ ∣ []
  ⊢ (Val ⟪ Θal , ` 1 ⇒ `ℕ ⟫) ⟪ Θ★ , ` 0 ⇒ ` 2 ⟫ ⦂ (` 0 ⇒ ` 1)
⊢redex-al =
  env bwf-Θ★ (sc-⇒ (sc-var hereᵒ) (sc-var (thereᵒ (thereᵒ hereᵒ))))
      (env (bwf⋆ (bwf↓x herex refl sk-var (wf-var here-abst) bwf[]))
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) sc-ℕ)
           (⊢ƛ (wf-var here-abst) ⊢$))

_ : Θal ⊕ Θ★ ≡ rvl⋆ ∷ cnc 1 `ℕ ∷ []
_ = refl

_ : mrgB Θal Θ★ (` 1 ⇒ `ℕ) ≡ (` 0 ⇒ `ℕ)
_ = refl

_ : baseS (Θal ⊕ Θ★) Γ★ ≡ blk ∷ blk ∷ ok ∷ []
_ = refl

¬sc-al : ¬ (Scoped (baseS (Θal ⊕ Θ★) Γ★) (mrgB Θal Θ★ (` 1 ⇒ `ℕ)))
¬sc-al (sc-⇒ (sc-var ()) _)

-- THE REPAIR: re-reveal at Y (Θ★'s own rep) instead of keeping the ⋆-slot
Θal′ : BCtx
Θal′ = rvl (` 0) ∷ cnc 1 `ℕ ∷ []

_ : intOf Γ★ Θal′ ≡ intOf Γ★ Θ★                -- the same interior
_ = refl

_ : substᵗ (γᵇ Θal′) (` 0 ⇒ ` 2) ≡ substᵗ (γᵇ Θal) (` 1 ⇒ `ℕ)
_ = refl

_ : substᵗ (ρᵇ Θal′) (` 0 ⇒ ` 2) ≡ substᵗ (ρᵇ Θ★) (` 0 ⇒ ` 2)
_ = refl

⊢repair-al : Γ★ ∣ [] ⊢ Val ⟪ Θal′ , ` 0 ⇒ ` 2 ⟫ ⦂ (` 0 ⇒ ` 1)
⊢repair-al =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var (thereᵒ (thereᵒ hereᵒ))))
      (⊢ƛ (wf-var here-xrvld) ⊢$)

------------------------------------------------------------------------
-- §9e.  THE TOPLAS THREE-AGENT ADVERSARY (p. 1048–49), against the LIVE ⊕
-- (ported from notes/old/D1Probe.agda §5).
--
--   δ_i(t) = int , δ_j(s) = t , δ_k = ⊥ ,  the k-term ⌈⌈3_i⌉^t_i⌉^s_j
--
-- Their shape is CONCEAL-OF-CONCEAL, so our deleting cancel never fires on
-- it: ⊕ APPENDS both hidings and the middle agent's contribution survives
-- as the pushed-in rep.  It does not even reach Merge here, because ⊕-γ's
-- side condition (Θ₁ drops only slots Θ₂ reveals) fails — a sufficient
-- condition, not a necessary one, and this is the shape it over-refuses.
------------------------------------------------------------------------

Δag : TCtx                             -- s := t (0) , t := ℕ (1)
Δag = rvld (` 0) ∷ rvld `ℕ ∷ []

Θag-o Θag-i : BCtx
Θag-o = cnc 0 (` 0) ∷ []               -- agent j: hide s, rep t
Θag-i = cnc 0 `ℕ ∷ []                  -- agent i: hide t, rep ℕ

_ : intOf Δag Θag-o ≡ rvld `ℕ ∷ []
_ = refl

⊢Tag : Δag ∣ [] ⊢ (($ 3) ⟪ Θag-i , ` 0 ⟫) ⟪ Θag-o , ` 0 ⟫ ⦂ ` 0
⊢Tag = env (bwf↓ here (≡→≈ refl) (wf-var here-rvld) bwf[])
           (sc-var hereᵒ)
           (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

-- ⊕ APPENDS: no entry is deleted, so no authority is dropped
_ : Θag-i ⊕ Θag-o ≡ cnc 1 `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- the middle authority ("s is t") is what discharges the second conceal's
-- reversal premise, through Δag's own chain — the ≈Δ̄ congruence's job
mid-authority : `ℕ ≈Δ̄⟨ Δag ⟩ (` 1)
mid-authority = ≈unf refl

⊢merged-ag : Δag ∣ [] ⊢ ($ 3) ⟪ Θag-i ⊕ Θag-o , ` 0 ⟫ ⦂ ` 0
⊢merged-ag =
  env (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ
            (bwf↓ here mid-authority wf-ℕ bwf[]))
      (sc-var hereᵒ) ⊢$

-- *** THE OTHER HALF OF THE B₂′ DILEMMA. ***  On THIS shape the merged
-- boundary type that works is the mrg₂ (outer) one — ` 0, the concealed
-- variable itself — while the landed mrg₁ form gives the composite's
-- SECOND slot and the wrong external face.  §9c refutes mrg₂ and this
-- refutes mrg₁: NEITHER single transport is right everywhere, which is
-- exactly why the external face is a rule premise.
_ : substᵗ (mrg₂ Θag-i Θag-o) (` 0) ≡ ` 0
_ = refl

_ : mrgB Θag-i Θag-o (` 0) ≡ ` 1
_ = refl

ρ-mrg₂-ag : substᵗ (ρᵇ (Θag-i ⊕ Θag-o)) (substᵗ (mrg₂ Θag-i Θag-o) (` 0))
          ≡ substᵗ (ρᵇ Θag-o) (` 0)
ρ-mrg₂-ag = refl

¬ρ-mrgB-ag : ¬ (substᵗ (ρᵇ (Θag-i ⊕ Θag-o)) (mrgB Θag-i Θag-o (` 0))
                ≡ substᵗ (ρᵇ Θag-o) (` 0))
¬ρ-mrgB-ag ()

-- APPEND-ONLY, for the record, is still not available to US where the
-- cancel DOES fire: the appended boundary is inadmissible over any
-- exterior, because an inner conceal of an outer REVEAL points at a slot
-- that exists only in the composite's own reveal block.
Θ⊞ : BCtx
Θ⊞ = cnc 0 `ℕ ∷ rvl `ℕ ∷ []

¬bwf-append : ∀ {Ψ : TCtx} → Bwf [] Ψ Θ⊞ Θ⊞ → ⊥
¬bwf-append (bwf↓  () _ _ _)
¬bwf-append (bwf↓x () _ _ _ _)

-- and towers DO collapse to bare values where the composite empties: §9a's
-- cancel pair is the witness, and the BASE-face drop is what finishes it
-- (Drop$ — the composite's face is the resolved rep ℕ)
tower-collapses : [] ⊢ ($ 7) ⟪ Θ1c ⊕ Θ2c , mrgB Θ1c Θ2c (` 0) ⟫ -→ $ 7
tower-collapses = Drop$

------------------------------------------------------------------------
-- §9f.  §9d(i) IS REACHABLE — AND THE MACHINE IS STUCK THERE.
--
-- Jeremy's question at the Merge landing: why does the inner boundary say
-- ↑W:=ℕ instead of ↑W:=X?  Answer: a reveal's rep is minted by TyBeta as
-- the LITERAL type argument at the application site, and that site (T3
-- below) lies in the plain exterior, where the ΛX was already eliminated
-- at T1 — X is not a name there, so `ℕ is the only spelling of that type.
-- The witness form ↑W:=X is only WRITABLE inside ↑X:=ℕ's interior; where
-- the source can write ·[X], the landed ⊕ is exact.  The re-expression of
-- ℕ as X is the job of the CROSSING: T4's dual ↓X:=ℕ re-expresses the
-- crossing term's boundary TYPE, but not the reps of the boundaries
-- already inside the crossing term — exactly the gap Decision 5 names.
--
--   P = ((ΛX. λx:X. λf:X⇒ℕ. f·x) ·[X⇒(X⇒ℕ)⇒ℕ, ℕ] · 5)
--         · ((ΛW. λy:W. 3) ·[W⇒ℕ, ℕ])
--
--   T1 (TyBeta, X)  the package opens: ↑X:=ℕ is born
--   T2 (Wrap, 5)    5 crosses in as the abstract x: ↓X:=ℕ is born (dualᴳ)
--   T3 (TyBeta, W)  the client's Λ opens IN THE EXTERIOR: ↑W:=ℕ, forced
--   T4 (Wrap)       the client's function crosses in: the §9d(i) NESTING
--
-- After T4 the active redex, in ambient Δcx, is the §9d(i) term with its
-- argument —  (Vcx ⟪Θcx1⟫ ⟪Θcx2⟫) · (5 ⟪↓X:=ℕ, X⟫)  — and NO rule fires
-- (stuck-cx).  With the repaired boundary Θcx′ in its place, Wrap fires
-- and the program runs on to 3 (run-repair-cx).
------------------------------------------------------------------------

B∀pkg : Ty
B∀pkg = ` 0 ⇒ ((` 0 ⇒ `ℕ) ⇒ `ℕ)

pkgV : Term                              -- λx:X. λf:X⇒ℕ. f·x
pkgV = ƛ ` 0 ∙ (ƛ (` 0 ⇒ `ℕ) ∙ ((` 0) · (` 1)))

mkW : Term                               -- ΛW. λy:W. 3
mkW = Λ Vcx

V★cx : Term                              -- 5 ⟪ ↓X:=ℕ , X ⟫
V★cx = ($ 5) ⟪ Θcx2 , ` 0 ⟫

useW : Term                              -- T2's contractum, a value
useW = (ƛ (` 0 ⇒ `ℕ) ∙ ((` 0) · V★cx)) ⟪ Θcx1 , (` 0 ⇒ `ℕ) ⇒ `ℕ ⟫

cxP₀ cxP₁ cxP₂ cxP₃ cxP₄ : Term
cxP₀ = (((Λ pkgV) ·[ B∀pkg , `ℕ ]) · ($ 5)) · (mkW ·[ ` 0 ⇒ `ℕ , `ℕ ])
cxP₁ = ((pkgV ⟪ Θcx1 , B∀pkg ⟫) · ($ 5)) · (mkW ·[ ` 0 ⇒ `ℕ , `ℕ ])
cxP₂ = useW · (mkW ·[ ` 0 ⇒ `ℕ , `ℕ ])
cxP₃ = useW · (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
cxP₄ = (((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫) · V★cx)
         ⟪ Θcx1 , `ℕ ⟫

-- the source is a CLOSED plain System F program, typed at ℕ
⊢cxP₀ : [] ∣ [] ⊢ cxP₀ ⦂ `ℕ
⊢cxP₀ =
  ⊢· (⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst)
                        (⊢ƛ (wf-⇒ (wf-var here-abst) wf-ℕ)
                            (⊢· (⊢` here) (⊢` (there here))))))
                wf-ℕ)
          ⊢$)
      (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) ⊢$)) wf-ℕ)

-- the two old Wrap steps are now Peel + Beta; cxP₂ and cxP₄ are reached
-- unchanged
cxP₁½ cxP₃½ : Term
cxP₁½ = ((pkgV · V★cx) ⟪ Θcx1 , (` 0 ⇒ `ℕ) ⇒ `ℕ ⟫)
          · (mkW ·[ ` 0 ⇒ `ℕ , `ℕ ])
cxP₃½ = ((ƛ (` 0 ⇒ `ℕ) ∙ ((` 0) · V★cx))
          · ((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫))
        ⟪ Θcx1 , `ℕ ⟫

cx-step₁ : [] ⊢ cxP₀ -→ cxP₁
cx-step₁ = ξ-·-l (ξ-·-l (TyBeta (V-G G-ƛ)))

cx-step₂a : [] ⊢ cxP₁ -→ cxP₁½
cx-step₂a = ξ-·-l (Peel (V-G G-ƛ) V-$)

cx-step₂b : [] ⊢ cxP₁½ -→ cxP₂
cx-step₂b = ξ-·-l (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ (I-var z≤n))))

cx-step₃ : [] ⊢ cxP₂ -→ cxP₃
cx-step₃ = ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒) (TyBeta (V-G G-ƛ))

cx-step₄a : [] ⊢ cxP₃ -→ cxP₃½
cx-step₄a = Peel (V-G G-ƛ) (V-⟪⟫ (V-G G-ƛ) I-⇒)

cx-step₄b : [] ⊢ cxP₃½ -→ cxP₄
cx-step₄b = ξ-⟪⟫ (Beta (V-⟪⟫ (V-⟪⟫ (V-G G-ƛ) I-⇒) I-⇒))

-- the stuck term is WELL-TYPED at ℕ (⊢redex-cx is its function part)
⊢cxP₄ : [] ∣ [] ⊢ cxP₄ ⦂ `ℕ
⊢cxP₄ =
  env (bwf↑ wf-ℕ bwf[]) sc-ℕ
      (⊢· ⊢redex-cx
          (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$))

-- *** WHAT §9f USED TO SAY, AND WHAT IT SAYS NOW. ***  Under the
-- flatten-first design cxP₄ was STUCK: the only candidate on its active
-- redex was Merge via ξ-·-l, and MergeOK's external-face component is
-- ¬ext-cx above — a REACHABLE counterexample to type safety, which is
-- what forced Decision 5.  ¬ext-cx / ¬⊢merged-cx / ⊢repair-cx are kept
-- above as the permanent record of that, and §9g records why no ⊕
-- whatever could have repaired it.
--
-- UNDER PEEL cxP₄ STEPS, and runs to a value in three steps, all live
-- inhabitants below.  The peel crosses the argument 5 ⟪ ↓X:=ℕ , X ⟫
-- INWARD through the outer conceal, whose dual is the reveal ↑X:=ℕ
-- (dual-cx, §9h) — a LINEAGE pair, not a coincidence — and the inner
-- ƛ-bodied wrapper is then peeled and β-reduced in the ordinary way.  No
-- merge is performed anywhere; the resulting tower is a value.

cxP₅ cxP₅′ cxP₅″ cxP₆ cxP₇ : Term
cxP₅ = (((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
           · ((($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫))
         ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
cxP₅′ = (((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
            · (($ 5) ⟪ Θcx2 ⊕ Θcx1 , mrgB Θcx2 Θcx1 (` 0) ⟫))
          ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
cxP₅″ = (((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) · ($ 5))
          ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
cxP₆ = (((Vcx · (($ 5) ⟪ dualᴳ [] Θcx1 , ` 0 ⟫))
           ⟪ Θcx1 , `ℕ ⟫)
         ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
cxP₇ = ((($ 3) ⟪ Θcx1 , `ℕ ⟫) ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫

-- step 1: THE PEEL.  The argument crosses the outer conceal inward.
cx-step₅ : [] ⊢ cxP₄ -→ cxP₅
cx-step₅ = ξ-⟪⟫ (Peel (V-⟪⟫ (V-G G-ƛ) I-⇒) (V-⟪⟫ V-$ (I-var z≤n)))

-- *** WHERE DECISION 6 CHANGES THE RUN. ***  cxP₅'s argument is the
-- lineage tower (5 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫, whose OUTER face is a
-- REVEAL variable — ACTIVE.  So it is NOT a value, Peel cannot consume
-- it, and ξ-·-r + Merge is the UNIQUE step (this is exactly §9j's old
-- clash, now decided).  The pair cancels to the empty composite and the
-- base-faced residue drops, so two GC steps replace the old single Peel.
cx-step₆a : [] ⊢ cxP₅ -→ cxP₅′
cx-step₆a = ξ-⟪⟫ (ξ-⟪⟫ (ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒)
  (Merge V-$ (I-var z≤n) (A-var (s≤s z≤n))
         (s≤s z≤n , bwf[] , sc-ℕ , ≼≈[] , refl))))

cx-step₆b : [] ⊢ cxP₅′ -→ cxP₅″
cx-step₆b = ξ-⟪⟫ (ξ-⟪⟫ (ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒) Drop$))

-- step 2: the argument is a value again — peel
cx-step₆ : [] ⊢ cxP₅″ -→ cxP₆
cx-step₆ = ξ-⟪⟫ (ξ-⟪⟫ (Peel (V-G G-ƛ) V-$))

-- step 3: β.  y is unused, so the crossed argument is discarded
cx-step₇ : [] ⊢ cxP₆ -→ cxP₇
cx-step₇ = ξ-⟪⟫ (ξ-⟪⟫ (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ (I-var z≤n)))))

-- … and cxP₇ IS NOT THE END ANY MORE.  All three of its faces are the
-- BASE type ℕ, hence ACTIVE, so the residual tower drops layer by layer
-- to the bare numeral: the program that used to get STUCK now answers 3
-- outright, with no wrapper left at all.
cx-step₈ : [] ⊢ cxP₇ -→ ((($ 3) ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫)
cx-step₈ = ξ-⟪⟫ (ξ-⟪⟫ Drop$)

cx-step₉ : [] ⊢ (($ 3) ⟪ Θcx2 , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫ -→ ($ 3) ⟪ Θcx1 , `ℕ ⟫
cx-step₉ = ξ-⟪⟫ Drop$

cx-step₁₀ : [] ⊢ ($ 3) ⟪ Θcx1 , `ℕ ⟫ -→ $ 3
cx-step₁₀ = Drop$

val-cx-answer : Value ($ 3)
val-cx-answer = V-$

-- CONTRAST, kept for the record: with the repaired boundary Θcx′
-- (↑W:=X , ↓X:=ℕ — the merge Decision 5 asked ⊕ to compute) in place of
-- the un-mergeable nesting, the peel fires there too
run-repair-cx : Δcx ⊢ (Vcx ⟪ Θcx′ , ` 0 ⇒ `ℕ ⟫) · V★cx
                  -→ (Vcx · (V★cx ⟪ dualᴳ Δcx Θcx′
                                  , renameᵗ (swapᵇ Θcx′) (` 0) ⟫))
                     ⟪ Θcx′ , `ℕ ⟫
run-repair-cx = Peel (V-G G-ƛ) (V-⟪⟫ V-$ (I-var z≤n))

-- …and the repaired run CONTINUES PAST the package reveal.  The residual
-- nesting is base-faced at BOTH levels, so under Decision 6 it is not a
-- merge redex at all: each layer is ACTIVE and is simply dropped, and the
-- run ends at the bare 3 rather than at 3 ⟪ ↑W:=ℕ , ℕ ⟫.  (The MergeOK
-- package for that nesting was fully discharged and is kept below as
-- run-repair-ok: the resolved spelling ℕ is CORRECT in the plain
-- exterior — it was wrong only across ↓X:=ℕ, which is Decision 5 in one
-- example.)
run-repair-tail : [] ⊢ (($ 3) ⟪ Θcx′ , `ℕ ⟫) ⟪ Θcx1 , `ℕ ⟫
                    -→ ($ 3) ⟪ Θcx1 , `ℕ ⟫
run-repair-tail = ξ-⟪⟫ Drop$

run-repair-end : [] ⊢ ($ 3) ⟪ Θcx1 , `ℕ ⟫ -→ $ 3
run-repair-end = Drop$

run-repair-ok : MergeOK [] Θcx′ Θcx1 `ℕ `ℕ
run-repair-ok =
  s≤s z≤n , bwf↑ wf-ℕ bwf[] , sc-ℕ ,
  ≼≈rvld ≼≈[] (≡→≈ refl) , refl

------------------------------------------------------------------------
-- §9g.  JEREMY'S OBSERVATION AT THE §9f REVIEW, SHARPENED AND CHECKED.
--
-- The observation: "W and X are not really tied to each other, they just
-- both happen to have the same rep type — a revealed W can line up with
-- a concealed X."  And its corollary: "the merge operator needs to know
-- the face types, because it's the face types that cause W and X to be
-- linked."
--
-- Both are confirmed here, and the second has a machine-checked LIMIT.
--
-- (i) The linkage is a COINCIDENCE OF REPS, stipulated positionally by
-- the outer boundary type — NOT a lineage.  (Contrast the x-pair
-- cancels, which ARE lineage: xrep-stored ties the dual's conceal to
-- the very reveal it was born from.)  So a correct ⊕ cannot be
-- face-blind: the landed ⊕ : BCtx → BCtx → BCtx never consults B₁/B₂,
-- which is exactly why the face equation had to be a MergeOK premise.
--
-- (ii) THE LIMIT: if the linkage is coincidence, one revealed W can
-- coincide with TWO different conceals at once — and then NO single
-- flat boundary exists, face-aware or not.  Take the double package
-- (the §9f construction with two abstractions, client's Λ still opened
-- outside):
--
--   (ΛX. ΛZ. λx:X. λg:X⇒Z. g·x) ·[ℕ] ·[ℕ] · 5 · ((ΛW. λy:W. y) ·[ℕ])
--
-- After the two TyBetas, Wrap(5), and the client's exterior TyBeta(W),
-- the client crosses the double reveal: the dual mints ↓X:=ℕ , ↓Z:=ℕ at
-- boundary type X⇒Z around (λy:W. y) ⟪ ↑W:=ℕ , W⇒W ⟫.  The external
-- face needs W ↦ X at the domain and W ↦ Z at the codomain: a single
-- reveal entry cannot carry both, rewriting B₀ instead breaks the
-- INTERNAL face against the body's type W⇒W (terms are never rewritten,
-- so the body stays typed at W⇒W), and splitting the reveal in two is
-- barred for the same reason.  Merge — under ANY ⊕ — cannot fire here:
-- flattening is IMPOSSIBLE, not just underdetermined.  NestedApp needs
-- a non-Merge answer on this shape.
------------------------------------------------------------------------

Δd : TCtx                              -- ambient: the two reveals' interior
Δd = rvld `ℕ ∷ rvld `ℕ ∷ []

Θd2 : BCtx                             -- ↓X:=ℕ , ↓Z:=ℕ (the double dual)
Θd2 = cnc 0 `ℕ ∷ cnc 1 `ℕ ∷ []

Θd1 : BCtx                             -- ↑W:=ℕ (client, exterior-born)
Θd1 = rvl `ℕ ∷ []

Vd : Term                              -- λy:W. y
Vd = ƛ ` 0 ∙ ` 0

Bd1 Bd2 : Ty
Bd1 = ` 0 ⇒ ` 0                        -- W⇒W
Bd2 = ` 0 ⇒ ` 1                        -- X⇒Z

-- the nesting TYPES: one client reveal against TWO equal-rep conceals
⊢redex-d : Δd ∣ [] ⊢ (Vd ⟪ Θd1 , Bd1 ⟫) ⟪ Θd2 , Bd2 ⟫ ⦂ Bd2
⊢redex-d =
  env (bwf↓ here (≡→≈ refl) wf-ℕ
        (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var (thereᵒ hereᵒ)))
      (env (bwf↑ wf-ℕ bwf[])
           (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
           (⊢ƛ (wf-var here-rvld) (⊢` here)))

-- the landed (face-blind) ⊕ exports ℕ⇒ℕ where the redex has X⇒Z
¬ext-d : ¬ (substᵗ (ρᵇ (Θd1 ⊕ Θd2)) (mrgB Θd1 Θd2 Bd1)
            ≡ substᵗ (ρᵇ Θd2) Bd2)
¬ext-d ()

-- the two FACE-DIRECTED single-rep candidates — re-abstract W at X, or
-- at Z: each fixes ONE position of the external face and breaks the other
ΘdX ΘdZ : BCtx
ΘdX = rvl (` 0) ∷ cnc 0 `ℕ ∷ cnc 1 `ℕ ∷ []
ΘdZ = rvl (` 1) ∷ cnc 0 `ℕ ∷ cnc 1 `ℕ ∷ []

¬ext-dX : ¬ (substᵗ (ρᵇ ΘdX) Bd1 ≡ substᵗ (ρᵇ Θd2) Bd2)
¬ext-dX ()

¬ext-dZ : ¬ (substᵗ (ρᵇ ΘdZ) Bd1 ≡ substᵗ (ρᵇ Θd2) Bd2)
¬ext-dZ ()

-- and REWRITING B₀ to spell the external face breaks the INTERNAL one
-- against the body's type W⇒W: any B₀ position that is not the reveal's
-- own variable γ-reads to ℕ, never to W
¬γ-dXZ : ¬ (substᵗ (γᵇ ΘdX) (` 1 ⇒ ` 2) ≡ substᵗ (γᵇ Θd1) Bd1)
¬γ-dXZ ()

¬γ-dWZ : ¬ (substᵗ (γᵇ ΘdX) (` 0 ⇒ ` 2) ≡ substᵗ (γᵇ Θd1) Bd1)
¬γ-dWZ ()

-- *** AND YET IT RUNS. ***  The shape on which flattening is IMPOSSIBLE is
-- an ordinary Peel redex: the outer boundary type is ⇒-shaped, so the
-- argument simply crosses inward.  The dual of the DOUBLE conceal is the
-- DOUBLE reveal ↑X:=ℕ , ↑Z:=ℕ — two lineage pairs, minted from the very
-- conceals they face — so nothing has to be re-abstracted outward and the
-- W-vs-{X,Z} coincidence is never consulted.  Three steps to a value.

Wd : Term                              -- a value at the domain type X
Wd = ($ 7) ⟪ Θd2 , ` 0 ⟫

bwf-Θd2 : Δd ∣ intOf Δd Θd2 ⊢ᵇ Θd2
bwf-Θd2 = bwf↓ here (≡→≈ refl) wf-ℕ
            (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ bwf[])

⊢Wd : Δd ∣ [] ⊢ Wd ⦂ ` 0
⊢Wd = env bwf-Θd2 (sc-var hereᵒ) ⊢$

-- the dual of the double conceal is the DOUBLE REVEAL
dual-d : dualᴳ Δd Θd2 ≡ (rvl `ℕ ∷ rvl `ℕ ∷ [])
dual-d = refl

run-d₁ : Δd ⊢ ((Vd ⟪ Θd1 , Bd1 ⟫) ⟪ Θd2 , Bd2 ⟫) · Wd
           -→ ((Vd ⟪ Θd1 , Bd1 ⟫)
                 · (Wd ⟪ dualᴳ Δd Θd2 , ` 0 ⟫)) ⟪ Θd2 , ` 1 ⟫
run-d₁ = Peel (V-⟪⟫ (V-G G-ƛ) I-⇒) (V-⟪⟫ V-$ (I-var z≤n))

-- *** DECISION 6 INSERTS THE COLLAPSE HERE. ***  The crossed argument
-- Wd ⟪ ↑X:=ℕ , ↑Z:=ℕ , X ⟫ has a REVEAL-VARIABLE outer face — ACTIVE —
-- around the INERT conceal face of Wd itself, so it is not a value and
-- the next Peel cannot consume it.  The lineage collapse fires first (the
-- double dual cancels the double reveal exactly: the composite is EMPTY),
-- and the base-faced residue then drops to the bare numeral.
run-d₁a : Δd ⊢ ((Vd ⟪ Θd1 , Bd1 ⟫)
                  · (Wd ⟪ dualᴳ Δd Θd2 , ` 0 ⟫)) ⟪ Θd2 , ` 1 ⟫
            -→ ((Vd ⟪ Θd1 , Bd1 ⟫)
                  · (($ 7) ⟪ Θd2 ⊕ dualᴳ Δd Θd2
                           , mrgB Θd2 (dualᴳ Δd Θd2) (` 0) ⟫))
               ⟪ Θd2 , ` 1 ⟫
run-d₁a = ξ-⟪⟫ (ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒)
  (Merge V-$ (I-var z≤n) (A-var (s≤s z≤n))
         (s≤s (s≤s z≤n) , bwf[] , sc-ℕ , ≼≈[] , refl)))

run-d-∅ : Θd2 ⊕ dualᴳ Δd Θd2 ≡ []
run-d-∅ = refl

run-d₁b : Δd ⊢ ((Vd ⟪ Θd1 , Bd1 ⟫)
                  · (($ 7) ⟪ Θd2 ⊕ dualᴳ Δd Θd2
                           , mrgB Θd2 (dualᴳ Δd Θd2) (` 0) ⟫))
               ⟪ Θd2 , ` 1 ⟫
            -→ ((Vd ⟪ Θd1 , Bd1 ⟫) · ($ 7)) ⟪ Θd2 , ` 1 ⟫
run-d₁b = ξ-⟪⟫ (ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒) Drop$)

run-d₂ : Δd ⊢ ((Vd ⟪ Θd1 , Bd1 ⟫) · ($ 7)) ⟪ Θd2 , ` 1 ⟫
           -→ ((Vd · (($ 7) ⟪ dualᴳ (intOf Δd Θd2) Θd1 , ` 0 ⟫))
                ⟪ Θd1 , ` 0 ⟫) ⟪ Θd2 , ` 1 ⟫
run-d₂ = ξ-⟪⟫ (Peel (V-G G-ƛ) V-$)

run-d₃ : Δd ⊢ ((Vd · (($ 7) ⟪ dualᴳ (intOf Δd Θd2) Θd1 , ` 0 ⟫))
                ⟪ Θd1 , ` 0 ⟫) ⟪ Θd2 , ` 1 ⟫
           -→ ((($ 7) ⟪ dualᴳ (intOf Δd Θd2) Θd1 , ` 0 ⟫)
                ⟪ Θd1 , ` 0 ⟫) ⟪ Θd2 , ` 1 ⟫
run-d₃ = ξ-⟪⟫ (ξ-⟪⟫ (Beta (V-⟪⟫ V-$ (I-var z≤n))))

------------------------------------------------------------------------
-- §9h.  AFTER A PEEL, EVERYTHING ELSE IS ALREADY LANDED — NOW LIVE.  The
-- rule (DECISIONS "Decision 5, REFRAMED", fork (b)) generalizes Wrap from
-- ƛ-bodied to VALUE-bodied wrappers, and is INSTALLED:
--
--   Peel : Value V → Value W → (V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
--        -→ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫
--
-- On §9f's once-stuck redex, Θ = Θcx2 = ↓X:=ℕ and dualᴳ Δcx Θcx2 = ↑X:=ℕ
-- (= Θcx1, definitionally — dual-cx), so the peel moves the argument
-- 5 ⟪ ↓X:=ℕ , X ⟫ INWARD, wrapping it in ↑X:=ℕ: a LINEAGE pair (the
-- reveal is minted from the very conceal it faces), no coincidence
-- linkage, no outward re-abstraction, no face-directed ⊕.  The whole run
-- is cx-step₅ … cx-step₁₀ in §9f; what is recorded HERE is that the
-- lineage pair the peel creates is exactly the pair Merge and Drop$
-- collect.  Under Decision 6 that collection is NOT optional any more:
-- the pair's outer face is a REVEAL VARIABLE, hence ACTIVE, so the tower
-- is not a value and the collapse is the machine's only move there.
------------------------------------------------------------------------

-- the peeled dual IS the reveal Θcx1, and its boundary type is X
dual-cx : dualᴳ Δcx Θcx2 ≡ Θcx1
dual-cx = refl

swap-cx : renameᵗ (swapᵇ Θcx2) (` 0) ≡ ` 0
swap-cx = refl

-- COLLAPSE step A (Merge, ambient = the peel boundary's interior []):
-- the lineage pair ↓X:=ℕ under ↑X:=ℕ cancels, MergeOK fully discharged.
-- The inner face ` 0 is INERT (Θcx2 reveals nothing) and the outer one
-- ACTIVE (0 < revs Θcx1 = 1) — the Decision-6 shape exactly.
peel-cancel : [] ⊢ (($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫
                -→ ($ 5) ⟪ Θcx2 ⊕ Θcx1 , mrgB Θcx2 Θcx1 (` 0) ⟫
peel-cancel = Merge V-$ (I-var z≤n) (A-var (s≤s z≤n))
  (s≤s z≤n , bwf[] , sc-ℕ , ≼≈[] , refl)

-- … and it is the UNIQUE step from that tower (det), where before the
-- install the tower was a VALUE that also stepped (§9j)
peel-cancel-uniq : ∀ {M′} → [] ⊢ (($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫ -→ M′
  → M′ ≡ ($ 5) ⟪ Θcx2 ⊕ Θcx1 , mrgB Θcx2 Θcx1 (` 0) ⟫
peel-cancel-uniq st = det st peel-cancel

-- …and the composite is EMPTY: the crossing consumed both boundaries
peel-∅ : Θcx2 ⊕ Θcx1 ≡ []
peel-∅ = refl

peel-drop : [] ⊢ ($ 5) ⟪ [] , mrgB Θcx2 Θcx1 (` 0) ⟫ -→ ($ 5)
peel-drop = Drop$

-- COLLAPSE step B: with the pair collected the inner wrapper's argument
-- is the bare 5, and the peel fires (cx-step₆).
peel-wrap : [] ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) · ($ 5)
              -→ (Vcx · (($ 5) ⟪ dualᴳ [] Θcx1 , ` 0 ⟫)) ⟪ Θcx1 , `ℕ ⟫
peel-wrap = Peel (V-G G-ƛ) V-$

------------------------------------------------------------------------
-- §9i.  THE ONE PLACE PEEL DOES NOT REACH: A REVEAL-VARIABLE FACE.
--
-- Peel and TyPeel push an elimination INWARD.  That is impossible when
-- the boundary type is one of the boundary's own REVEAL VARIABLES ` X,
-- because then the two faces are
--
--   internal:  γᵇ Θ X = ` X          (γᵇ-lo)
--   external:  ρᵇ Θ X = repOf X Θ    (⇒-shaped, or the redex would not
--                                     type)
--
-- so the wrapped value has ABSTRACT type inside and no elimination of it
-- is typable.  Re-spelling the boundary type as the rep is barred by
-- §9g's ¬γ argument (the body is typed at ` X on the nose and terms are
-- never rewritten).  The only move left is to COLLAPSE the nesting —
-- canon-var says the body is a wrapper — i.e. Merge.
--
-- AND THE SHAPE IS REACHABLE, from a closed plain System F source, by
-- PEEL STEPS ONLY.  The package's ∀-body returns the abstract X:
--
--   Q = ((ΛX. λf:(ℕ⇒X). f · 3) ·[ (ℕ⇒X)⇒X , ℕ⇒ℕ ] · g) · 5
--       g = λn:ℕ. λm:ℕ. 7
--
--   R1 TyBeta(X)   ↑X:=ℕ⇒ℕ is born
--   R2 Peel(g)     g crosses in; the dual ↓X:=ℕ⇒ℕ is minted
--   R3 Beta        f := the crossed g
--   R4 Peel(3)     3 crosses the dual inward
--   R5 Beta        g's body — a ƛ — is left UNDER THE DUAL
--
-- and R5's term is  (((λm:ℕ.7) ⟪ ↓X:=ℕ⇒ℕ , X ⟫) ⟪ ↑X:=ℕ⇒ℕ , X ⟫) · 5 :
-- a reveal-variable face, with a LINEAGE pair inside it.  rv-only-merge
-- is the machine-checked statement that EVERY step from it is a Merge —
-- delete Merge and the calculus is STUCK here, so progress needs it.
------------------------------------------------------------------------

Θr Θrᵈ : BCtx
Θr  = rvl (`ℕ ⇒ `ℕ) ∷ []               -- ↑X:=ℕ⇒ℕ
Θrᵈ = cnc 0 (`ℕ ⇒ `ℕ) ∷ []             -- ↓X:=ℕ⇒ℕ (its dual)

Bpkg-rv : Ty                           -- (ℕ⇒X)⇒X
Bpkg-rv = (`ℕ ⇒ ` 0) ⇒ ` 0

pkgV-rv : Term                         -- λf:(ℕ⇒X). f · 3
pkgV-rv = ƛ (`ℕ ⇒ ` 0) ∙ ((` 0) · ($ 3))

g-rv : Term                            -- λn:ℕ. λm:ℕ. 7
g-rv = ƛ `ℕ ∙ (ƛ `ℕ ∙ ($ 7))

Ψr : TCtx                              -- the reveal's interior
Ψr = rvld (`ℕ ⇒ `ℕ) ∷ []

rvQ₀ rvQ₁ rvQ₂ rvQ₃ rvQ₄ rvQ₅ : Term
rvQ₀ = (((Λ pkgV-rv) ·[ Bpkg-rv , `ℕ ⇒ `ℕ ]) · g-rv) · ($ 5)
rvQ₁ = ((pkgV-rv ⟪ Θr , Bpkg-rv ⟫) · g-rv) · ($ 5)
rvQ₂ = ((pkgV-rv · (g-rv ⟪ Θrᵈ , `ℕ ⇒ ` 0 ⟫)) ⟪ Θr , ` 0 ⟫) · ($ 5)
rvQ₃ = (((g-rv ⟪ Θrᵈ , `ℕ ⇒ ` 0 ⟫) · ($ 3)) ⟪ Θr , ` 0 ⟫) · ($ 5)
rvQ₄ = (((g-rv · (($ 3) ⟪ Θr , `ℕ ⟫)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫)
         · ($ 5)
rvQ₅ = (((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫) · ($ 5)

-- a closed plain System F source, typed at ℕ
⊢rvQ₀ : [] ∣ [] ⊢ rvQ₀ ⦂ `ℕ
⊢rvQ₀ =
  ⊢· (⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-⇒ wf-ℕ (wf-var here-abst))
                       (⊢· (⊢` here) ⊢$)))
               (wf-⇒ wf-ℕ wf-ℕ))
         (⊢ƛ wf-ℕ (⊢ƛ wf-ℕ ⊢$)))
     ⊢$

rv-step₁ : [] ⊢ rvQ₀ -→ rvQ₁
rv-step₁ = ξ-·-l (ξ-·-l (TyBeta (V-G G-ƛ)))

rv-step₂ : [] ⊢ rvQ₁ -→ rvQ₂
rv-step₂ = ξ-·-l (Peel (V-G G-ƛ) (V-G G-ƛ))

rv-step₃ : [] ⊢ rvQ₂ -→ rvQ₃
rv-step₃ = ξ-·-l (ξ-⟪⟫ (Beta (V-⟪⟫ (V-G G-ƛ) I-⇒)))

rv-step₄ : [] ⊢ rvQ₃ -→ rvQ₄
rv-step₄ = ξ-·-l (ξ-⟪⟫ (Peel (V-G G-ƛ) V-$))

-- the crossed argument 3 ⟪ ↑X:=ℕ⇒ℕ , ℕ ⟫ has a BASE face — ACTIVE — so
-- under Decision 6 it drops before the β, one extra step
rvQ₄′ : Term
rvQ₄′ = (((g-rv · ($ 3)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫) · ($ 5)

rv-step₄a : [] ⊢ rvQ₄ -→ rvQ₄′
rv-step₄a = ξ-·-l (ξ-⟪⟫ (ξ-⟪⟫ (ξ-·-r (V-G G-ƛ) Drop$)))

rv-step₅ : [] ⊢ rvQ₄′ -→ rvQ₅
rv-step₅ = ξ-·-l (ξ-⟪⟫ (ξ-⟪⟫ (Beta V-$)))

-- the inner conceal really is the peel's own dual — a LINEAGE pair
dual-rv : dualᴳ Ψr Θrᵈ ≡ Θr
dual-rv = refl

-- rvQ₅ is well typed at ℕ …
⊢rvQ₅ : [] ∣ [] ⊢ rvQ₅ ⦂ `ℕ
⊢rvQ₅ =
  ⊢· (env (bwf↑ (wf-⇒ wf-ℕ wf-ℕ) bwf[]) (sc-var hereᵒ)
          (env (bwf↓ here (≡→≈ refl) (wf-⇒ wf-ℕ wf-ℕ) bwf[])
               (sc-var hereᵒ)
               (⊢ƛ wf-ℕ ⊢$)))
     ⊢$

-- … it is not a value, and EVERY step it can take is a Merge on its
-- function part: Peel cannot fire (the boundary type is ` 0, not
-- ⇒-shaped), Beta cannot (no bare ƛ in function position), Drop$ cannot
-- (neither face is a base type), ξ-⟪⟫ cannot (the innermost body is a ƛ)
-- and ξ-·-r cannot (the argument is a numeral).  Under Decision 6 the
-- tower is moreover NOT A VALUE (¬val-rv): its outer face ` 0 is a
-- reveal variable of Θr, hence ACTIVE — which is why the collapse is
-- forced rather than optional, and why nothing competes with it.
rv-only-merge : ∀ {M′} → [] ⊢ rvQ₅ -→ M′
  → Σ BCtx λ Θ₁ → Σ BCtx λ Θ₂ → Σ Ty λ B₁ → Σ Ty λ B₂
      → MergeOK [] Θ₁ Θ₂ B₁ B₂
rv-only-merge (ξ-·-l (Merge v i a mok)) = Θrᵈ , Θr , ` 0 , ` 0 , mok
rv-only-merge (ξ-·-l (ξ-⟪⟫ (ξ-⟪⟫ ())))
rv-only-merge (ξ-·-r v ())

-- and the Merge DOES fire, MergeOK fully discharged: the lineage pair
-- cancels to the empty boundary and X's rep resolves to ℕ⇒ℕ
rv-merge : [] ⊢ ((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫
             -→ (ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫
rv-merge = Merge (V-G G-ƛ) (I-var z≤n) (A-var (s≤s z≤n))
  (s≤s z≤n , bwf[] , sc-⇒ sc-ℕ sc-ℕ , ≼≈[] , refl)

-- the tower is not a value, so the collapse has no competitor …
¬val-rv : ¬ Value (((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫)
¬val-rv (V-⟪⟫ _ (I-var ()))

-- … and it is the UNIQUE step, by det
rv-merge-uniq : ∀ {M′}
  → [] ⊢ ((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫ -→ M′
  → M′ ≡ (ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫
rv-merge-uniq st = det st rv-merge

rv-⊕-∅ : Θrᵈ ⊕ Θr ≡ []
rv-⊕-∅ = refl

rv-mrgB : mrgB Θrᵈ Θr (` 0) ≡ (`ℕ ⇒ `ℕ)
rv-mrgB = refl

-- after the cancel the ordinary Peel finishes the program
rv-finish : [] ⊢ ((ƛ `ℕ ∙ ($ 7)) ⟪ [] , `ℕ ⇒ `ℕ ⟫) · ($ 5)
              -→ ((ƛ `ℕ ∙ ($ 7)) · (($ 5) ⟪ [] , `ℕ ⟫)) ⟪ [] , `ℕ ⟫
rv-finish = Peel (V-G G-ƛ) V-$

-- … AND THE RUN NOW REACHES THE BARE ANSWER.  Every residual boundary
-- left by the peel has a BASE face, so each one drops: the program ends
-- at 7, not at a wrapper around 7.  (Before the install the ∅-boundaries
-- needed Drop∅ and the ℕ-faced ones had no rule at all.)
rv-fin₂ : [] ⊢ ((ƛ `ℕ ∙ ($ 7)) · (($ 5) ⟪ [] , `ℕ ⟫)) ⟪ [] , `ℕ ⟫
            -→ ((ƛ `ℕ ∙ ($ 7)) · ($ 5)) ⟪ [] , `ℕ ⟫
rv-fin₂ = ξ-⟪⟫ (ξ-·-r (V-G G-ƛ) Drop$)

rv-fin₃ : [] ⊢ ((ƛ `ℕ ∙ ($ 7)) · ($ 5)) ⟪ [] , `ℕ ⟫ -→ ($ 7) ⟪ [] , `ℕ ⟫
rv-fin₃ = ξ-⟪⟫ (Beta V-$)

rv-fin₄ : [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ -→ $ 7
rv-fin₄ = Drop$

------------------------------------------------------------------------
-- §9j.  DETERMINISM — *** RESTORED BY DECISION 6 ***.
--
-- What this section used to record: Merge and Drop∅ were the only rules
-- whose left-hand side was a VALUE, so
--
--   * VALUES DID STEP (val-cancel / val-steps), making
--     `Value V → ¬ (Δ ⊢ V -→ M′)` FALSE; and
--   * REDUCTION WAS NONDETERMINISTIC (nd-peel / nd-merge / nd-≢): at an
--     application whose ARGUMENT was a cancellable lineage pair, ξ-·-r's
--     Value premise was satisfied AND the argument stepped, so Merge
--     competed with the Peel on the very same term.
--
-- The ACTIVE/INERT value restriction removes the premise of both: the
-- clashing tower's outer face is a REVEAL VARIABLE, hence ACTIVE, so it
-- is not a value at all.  `V-¬-→` and `det` are now THEOREMS in
-- strong.BReduction, and what is recorded here is the CONVERSE of what
-- was recorded before — the once-clashing terms have UNIQUE steps.
------------------------------------------------------------------------

-- the once-offending "value" is NOT a value: 0 < revs Θcx1 = 1
¬val-cancel : ¬ Value ((($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫)
¬val-cancel (V-⟪⟫ _ (I-var ()))

-- so at the application the Peel is DEAD (its Value premise cannot be
-- met) and ξ-·-r + Merge is the only move …
nd-arg : [] ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
                · ((($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫)
           -→ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
                · (($ 5) ⟪ Θcx2 ⊕ Θcx1 , mrgB Θcx2 Θcx1 (` 0) ⟫)
nd-arg = ξ-·-r (V-⟪⟫ (V-G G-ƛ) I-⇒) peel-cancel

-- … and it is THE step: everything else that used to compete is now
-- refuted by det
nd-arg-uniq : ∀ {M′}
  → [] ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
           · ((($ 5) ⟪ Θcx2 , ` 0 ⟫) ⟪ Θcx1 , ` 0 ⟫) -→ M′
  → M′ ≡ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫)
           · (($ 5) ⟪ Θcx2 ⊕ Θcx1 , mrgB Θcx2 Θcx1 (` 0) ⟫)
nd-arg-uniq st = det st nd-arg

-- the two general laws, cited at this file's own shapes
values-dont-step : ∀ {Δ V M′} → Value V → Δ ⊢ V -→ M′ → ⊥
values-dont-step = V-¬-→

determinism : ∀ {Δ M M₁ M₂} → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂
determinism = det

------------------------------------------------------------------------
-- §9k.  THE FACE-TYPE RESTRICTION, AS RULED.
--
-- What this section used to record: restricting Merge to ⇒ / ∀ faces
-- does NOT restore determinism, because §9i's own tower has EXTERNAL
-- type ℕ⇒ℕ and, being a value, clashed with Beta in argument position
-- (nd-beta / nd-mergeArg / nd-fnface-≢).  Decision 6 rules the OTHER
-- way round — the merge is restricted to the faces that are ACTIVE, i.e.
-- the REVEAL VARIABLES, which is the complement of Peel/TyPeel's
-- syntactic ⇒ / ∀ — and the clash disappears for the reason the section
-- said it could not: a merge redex is no longer a value.
--
-- The exit §9k warned about ("excluding ⇒/∀-faced merge-redexes from
-- Value revives §9d(i)") is also closed: ⊢redex-cx's ⇒ face is INERT, so
-- that nesting is a VALUE at rest and needs no MergeOK at all — its
-- boundaries are consumed one layer per application by Peel.
------------------------------------------------------------------------

Trv : Term                              -- §9i's tower; external type ℕ⇒ℕ
Trv = ((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ , ` 0 ⟫) ⟪ Θr , ` 0 ⟫

nd-fnface : Term
nd-fnface = (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · ($ 5))) · Trv

-- Beta is DEAD here: Trv's outer face is a reveal variable, so Trv is not
-- a value and the Beta premise cannot be met (¬val-rv, §9i)
nd-beta-dead : ¬ Value Trv
nd-beta-dead = ¬val-rv

-- the merge in argument position is the unique step
nd-mergeArg : [] ⊢ nd-fnface
   -→ (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · ($ 5)))
      · ((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫)
nd-mergeArg = ξ-·-r (V-G G-ƛ) rv-merge

nd-mergeArg-uniq : ∀ {M′} → [] ⊢ nd-fnface -→ M′
  → M′ ≡ (ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · ($ 5)))
           · ((ƛ `ℕ ∙ ($ 7)) ⟪ Θrᵈ ⊕ Θr , mrgB Θrᵈ Θr (` 0) ⟫)
nd-mergeArg-uniq st = det st nd-mergeArg

-- and §9d(i)'s once-unmergeable ⇒-faced nesting is simply a VALUE
val-redex-cx : Value ((Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫)
val-redex-cx = V-⟪⟫ (V-⟪⟫ (V-G G-ƛ) I-⇒) I-⇒

redex-cx-¬-→ : ∀ {M′}
  → Δcx ⊢ (Vcx ⟪ Θcx1 , ` 0 ⇒ `ℕ ⟫) ⟪ Θcx2 , ` 0 ⇒ `ℕ ⟫ -→ M′ → ⊥
redex-cx-¬-→ = V-¬-→ val-redex-cx

------------------------------------------------------------------------
-- §9l.  *** THE DECISION-6 RESIDUE, AND A COUNTEREXAMPLE TO IT. ***
--
-- After the install, progress has exactly ONE open obligation
-- (strong.ProgressDef's MergeDerivable, the paper's applyCast totality):
-- at a well-typed nesting
--
--   (V ⟪ Θ₁ , ` Y ⟫) ⟪ Θ₂ , ` X ⟫      revs Θ₁ ≤ Y ,  X < revs Θ₂
--
-- — a SEALED value inside an ACTIVE reveal-variable boundary — MergeOK
-- must be DERIVABLE.  Three instances are fully discharged (§9i's
-- rv-merge here, and CancelProbe's a-/p-/e-MergeOK, one per family).
--
-- IT IS NOT DERIVABLE IN GENERAL, and here is why, on one term.  Take an
-- ambient W:=𝔹, an outer boundary that reveals X:=ℕ, and an inner one
-- that conceals BOTH X and the ambient W:
--
--   Δp = W:=𝔹 ;  Θ₂ = ↑X:=ℕ ;  Θ₁ = ↓X:=ℕ , ↓W:=𝔹
--   (3 ⟪ Θ₁ , X ⟫) ⟪ Θ₂ , X ⟫  :  ℕ           -- ⊢p, below
--
-- The inner face is INERT (Θ₁ reveals nothing) and the outer one ACTIVE
-- (0 < revs Θ₂ = 1): this is exactly progress's shape, so the term is not
-- a value and Merge must fire.  But MergeOK's FIRST component is
-- cmax Θ₁ ≤ revs Θ₂, i.e. 2 ≤ 1 — FALSE, because Θ₁ drops the ambient
-- slot W, which Θ₂ does not reveal.  So the term is WELL TYPED, NOT A
-- VALUE, and TAKES NO STEP.
--
-- THE DIAGNOSIS IS SHARP, and it is not that the merge is wrong here.
-- Components (2)–(5) all hold ON THE NOSE (bwf-p / sc-p / int⊕-p /
-- ext-p), the composite is the single conceal ↓W:=𝔹, the contractum
-- types at the redex's own type (⊢merged-p) — and ⊕-γ's CONCLUSION, the
-- internal-face equation that component (1) exists to buy, holds too
-- (int-p).  Component (1) is ⊕-γ's SUFFICIENT side condition, not a
-- necessary one, and it is the sole obstruction.
--
-- INDICATED REPAIR (a Decision-3 change to MergeOK, NOT taken here):
-- replace component (1) by the internal-face equation it is used to
-- derive, keeping ⊕-γ as the theorem that discharges it whenever
-- cmax Θ₁ ≤ revs Θ₂ — every existing MergeOK witness then still builds,
-- and this counterexample dies.  Whether MergeDerivable becomes a
-- theorem under that MergeOK is the remaining question.
------------------------------------------------------------------------

Δp : TCtx
Δp = rvld `𝔹 ∷ []

Θ2p Θ1p : BCtx
Θ2p = rvl `ℕ ∷ []
Θ1p = cnc 0 `ℕ ∷ cnc 1 `𝔹 ∷ []

Ψ2p : TCtx
Ψ2p = intOf Δp Θ2p

_ : Ψ2p ≡ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

_ : intOf Ψ2p Θ1p ≡ []
_ = refl

_ : substᵗ (γᵇ Θ1p) (` 0) ≡ `ℕ
_ = refl

_ : substᵗ (ρᵇ Θ1p) (` 0) ≡ ` 0
_ = refl

_ : substᵗ (ρᵇ Θ2p) (` 0) ≡ `ℕ
_ = refl

_ : baseS Θ1p Ψ2p ≡ ok ∷ ok ∷ []
_ = refl

⊢p : Δp ∣ [] ⊢ (($ 3) ⟪ Θ1p , ` 0 ⟫) ⟪ Θ2p , ` 0 ⟫ ⦂ `ℕ
⊢p = env (bwf↑ wf-ℕ bwf[]) (sc-var hereᵒ)
         (env (bwf↓ here (≡→≈ refl) wf-ℕ
                    (bwf↓ (skip-rvld here) (≡→≈ refl) wf-𝔹 bwf[]))
              (sc-var hereᵒ)
              ⊢$)

-- it is progress's own shape: an INERT face inside an ACTIVE one
inert-p : Inert Θ1p (` 0)
inert-p = I-var z≤n

active-p : Active Θ2p (` 0)
active-p = A-var (s≤s z≤n)

-- … so it is NOT a value
¬val-p : ¬ Value ((($ 3) ⟪ Θ1p , ` 0 ⟫) ⟪ Θ2p , ` 0 ⟫)
¬val-p (V-⟪⟫ _ (I-var ()))

-- … and MergeOK's FIRST component is 2 ≤ 1
_ : cmax Θ1p ≡ 2
_ = refl

_ : revs Θ2p ≡ 1
_ = refl

¬le-p : ¬ (cmax Θ1p ≤ revs Θ2p)
¬le-p (s≤s ())

¬mok-p : ¬ (MergeOK Δp Θ1p Θ2p (` 0) (` 0))
¬mok-p (le , _) = ¬le-p le

-- EVERYTHING ELSE the merge needs is in place
_ : Θ1p ⊕ Θ2p ≡ cnc 0 `𝔹 ∷ []
_ = refl

_ : mrgB Θ1p Θ2p (` 0) ≡ `ℕ
_ = refl

-- ⊕-γ's CONCLUSION, although its side condition (component (1)) fails
int-p : substᵗ (γᵇ (Θ1p ⊕ Θ2p)) (mrgB Θ1p Θ2p (` 0))
        ≡ substᵗ (γᵇ Θ1p) (` 0)
int-p = refl

ext-p : substᵗ (ρᵇ (Θ1p ⊕ Θ2p)) (mrgB Θ1p Θ2p (` 0))
        ≡ substᵗ (ρᵇ Θ2p) (` 0)
ext-p = refl

sc-p : Scoped (baseS (Θ1p ⊕ Θ2p) Δp) (mrgB Θ1p Θ2p (` 0))
sc-p = sc-ℕ

int⊕-p : intOf (intOf Δp Θ2p) Θ1p ≼≈ intOf Δp (Θ1p ⊕ Θ2p)
int⊕-p = ≼≈[]

bwf-p : Δp ∣ intOf Δp (Θ1p ⊕ Θ2p) ⊢ᵇ (Θ1p ⊕ Θ2p)
bwf-p = bwf↓ here (≡→≈ refl) wf-𝔹 bwf[]

-- and the CONTRACTUM types, at the redex's own type
⊢merged-p : Δp ∣ [] ⊢ ($ 3) ⟪ Θ1p ⊕ Θ2p , mrgB Θ1p Θ2p (` 0) ⟫ ⦂ `ℕ
⊢merged-p = env bwf-p sc-p ⊢$
